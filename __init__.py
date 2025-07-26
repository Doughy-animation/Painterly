bl_info = {
    "name": "Painterly",
    "author": "Patrick Daugherty - Doughy Animation Studio",
    "version": (2, 8, 2),
    "blender": (4, 1, 0),
    "location": "View3D > Sidebar > Painterly",
    "description": ("Stylized painterly strokes and textures. "
                    "Create painterly strokes and normal map textures using handcrafted textures. Includes Geometry Node Mode."),
    "category": "3D View",
    "doc_url": "https://www.doughyanimation.com/painterly",
}

# Global version constant for UI display
CURRENT_VERSION = (2, 8, 2)
# URL for checking updates
UPDATE_JSON_URL = (
    "https://drive.google.com/uc?export=download"
    "&id=1_dfqAKgrEgpYKArZAZnQ8KtAVlCiYNe7"
)
import bpy
import os, random, subprocess, sys, time, math, json, urllib.request, shutil
import io, zipfile, hashlib, importlib, concurrent.futures, re
import numpy as np
from importlib import import_module, reload
from mathutils import Vector
from bpy.app.handlers import persistent
import bpy.utils.previews
import platform

from bpy.props import (
    IntProperty, FloatProperty, BoolProperty, EnumProperty,
    PointerProperty, StringProperty, CollectionProperty, FloatVectorProperty,
)

from bpy.types import (
    Panel, Operator, PropertyGroup, AddonPreferences, UILayout, Menu
)

# -------------------------------------------------------------------------
# Helper utilities
# -------------------------------------------------------------------------
def get_addon_key() -> str:
    """Return the module-name Blender registered this file under."""
    return __name__

def check_pillow() -> bool:
    import site
    user_site = site.getusersitepackages()
    if user_site not in sys.path:
        sys.path.append(user_site)
    try:
        import PIL
        return True
    except ImportError:
        return False

def atoi(text):
    return int(text) if text.isdigit() else text

def natural_keys(text):
    # Splits the text into a list of strings and integers.
    return [atoi(c) for c in re.split(r'(\d+)', text)]

def compare_versions(v1, v2):
    # Compare each number in the tuples
    for a, b in zip(v1, v2):
        if a < b:
            return -1
        if a > b:
            return 1
    # If one version is longer than the other:
    if len(v1) < len(v2):
        return -1
    elif len(v1) > len(v2):
        return 1
    return 0

# ---------------------------
# GLOBALS & DEBOUNCE VARIABLES
# ---------------------------
last_color_update_time = 0.0
pending_inactive_ramps = []
DEBOUNCE_INTERVAL = 0.1
DEBOUNCE_TOTAL_DELAY = 0.2
_in_update_color = False


# ---------------------------------------------------------------------------
# START: ROOT FOLDER PERSISTENCE & PREFERENCES
# This section implements the robust folder management system and preferences panel.
# ---------------------------------------------------------------------------

# ----- NEW ICON RELOAD CODE START -----

custom_icons = None

def reinitialize_page_icons(folder_collection, current_index, previews_per_page):
    """
    Wipes and rebuilds the preview-icon collection so that the correct
    JPEG thumbnails from each UI_IMAGE folder are displayed.
    """
    global custom_icons
    if custom_icons:
        bpy.utils.previews.remove(custom_icons)

    custom_icons = bpy.utils.previews.new()

    start = (current_index // previews_per_page) * previews_per_page
    end   = min(start + previews_per_page, len(folder_collection))

    for idx in range(start, end):
        item = folder_collection[idx]
        try:
            custom_icons.load(item.preview_image, item.preview_filepath, 'IMAGE')
        except Exception as e:
            print("Error loading preview:", e)


def scan_directory_recursive(base_dir, collection):
    """
    Recursively visits every sub-folder, looking for a “UI_IMAGE” dir
    containing JPEGs. The largest JPEG (by file size) is picked as
    that folder’s representative thumbnail.
    """
    global custom_icons
    if not os.path.exists(base_dir):
        return

    ui_img_path = os.path.join(base_dir, "UI_IMAGE")
    if os.path.isdir(ui_img_path):
        jpeg_files = [nm for nm in os.listdir(ui_img_path)
                      if nm.lower().endswith(('.jpg', '.jpeg'))]
        if jpeg_files:
            jpeg_files.sort(key=lambda nm:
                            os.path.getsize(os.path.join(ui_img_path, nm)),
                            reverse=True)
            nm      = jpeg_files[0]
            fullp   = os.path.join(ui_img_path, nm)
            iconkey = hashlib.md5(fullp.encode('utf-8')).hexdigest()

            if iconkey not in custom_icons:
                try:
                    custom_icons.load(iconkey, fullp, 'IMAGE')
                except Exception:
                    pass

            it                 = collection.add()
            it.name            = os.path.basename(base_dir)
            it.path            = base_dir
            it.category        = os.path.basename(base_dir)
            it.preview_image   = iconkey
            it.preview_filepath= fullp

    for sub_name in os.listdir(base_dir):
        if sub_name.lower() == "ui_image":
            continue
        sub_path = os.path.join(base_dir, sub_name)
        if os.path.isdir(sub_path):
            scan_directory_recursive(sub_path, collection)

def scan_painterly_folders(context):
    """
    Clears and rebuilds every CollectionProperty that backs the
    thumbnail browsers (Stroke Pen, Normal Maps, Presets).
    """
    global custom_icons
    if custom_icons:
        custom_icons.clear()

    props = context.scene.painterly_folder_properties
    addon = context.preferences.addons.get(get_addon_key())
    if not addon:
        return
    prefs = addon.preferences
    base_path = prefs.base_folder_path

    if not base_path or not os.path.exists(base_path):
        print("Invalid base path for Painterly folders.")
        return

    props.stroke_type_folders.clear()
    props.stroke_subtype_folders.clear()
    props.stroke_folders.clear()
    props.normal_map_folders.clear()
    props.preset_folders.clear()

    stroke_type_path = os.path.join(base_path, "Stroke Pen", "Stroke_Type")
    if os.path.exists(stroke_type_path):
        for cat in os.listdir(stroke_type_path):
            cpath = os.path.join(stroke_type_path, cat)
            if os.path.isdir(cpath) and cat.lower() != "ui_image":
                new_item          = props.stroke_type_folders.add()
                new_item.name     = cat
                new_item.path     = cpath
                new_item.category = cat
                ui_img_dir = os.path.join(cpath, "UI_IMAGE")
                if os.path.exists(ui_img_dir):
                    jpeg_files = [nm for nm in os.listdir(ui_img_dir)
                                  if nm.lower().endswith(('.jpg', '.jpeg'))]
                    if jpeg_files:
                        jpeg_files.sort(key=lambda nm:
                            os.path.getsize(os.path.join(ui_img_dir, nm)),
                            reverse=True)
                        nm      = jpeg_files[0]
                        fullp   = os.path.join(ui_img_dir, nm)
                        iconkey = hashlib.md5(fullp.encode('utf-8')).hexdigest()
                        if iconkey not in custom_icons:
                            try:
                                custom_icons.load(iconkey, fullp, 'IMAGE')
                            except:
                                pass
                        new_item.preview_image   = iconkey
                        new_item.preview_filepath= fullp

    props.selected_stroke_type  = "ALL"
    props.selected_stroke_subtype = "NA"
    props.update_main_folder(context)

    normal_path = os.path.join(base_path, "Stroke Pen", "Stroke Normal Maps")
    if os.path.exists(normal_path):
        for nmf in os.listdir(normal_path):
            npath = os.path.join(normal_path, nmf)
            if os.path.isdir(npath) and nmf.lower() != "ui_image":
                item          = props.normal_map_folders.add()
                item.name     = nmf
                item.path     = npath
                ui_img = os.path.join(npath, "UI_IMAGE")
                if os.path.exists(ui_img):
                    jpeg_files = [nn for nn in os.listdir(ui_img)
                                  if nn.lower().endswith(('.jpg', '.jpeg'))]
                    if jpeg_files:
                        jpeg_files.sort(key=lambda nn:
                            os.path.getsize(os.path.join(ui_img, nn)),
                            reverse=True)
                        nn      = jpeg_files[0]
                        fullp   = os.path.join(ui_img, nn)
                        iconkey = hashlib.md5(fullp.encode('utf-8')).hexdigest()
                        if iconkey not in custom_icons:
                            try:
                                custom_icons.load(iconkey, fullp, 'IMAGE')
                            except:
                                pass
                        item.preview_image   = iconkey
                        item.preview_filepath= fullp

    preset_path = os.path.join(base_path, "Painterly Texture", "Strokes")
    if os.path.exists(preset_path):
        for pcat in os.listdir(preset_path):
            ppath = os.path.join(preset_path, pcat)
            if os.path.isdir(ppath) and pcat.lower() != "ui_image":
                pi          = props.preset_folders.add()
                pi.name     = pcat
                pi.path     = ppath
                ui_img2 = os.path.join(ppath, "UI_IMAGE")
                if os.path.exists(ui_img2):
                    jpeg_files = [nn for nn in os.listdir(ui_img2)
                                  if nn.lower().endswith(('.jpg', '.jpeg'))]
                    if jpeg_files:
                        jpeg_files.sort(key=lambda nn:
                            os.path.getsize(os.path.join(ui_img2, nn)),
                            reverse=True)
                        nn      = jpeg_files[0]
                        fullp   = os.path.join(ui_img2, nn)
                        iconkey2= hashlib.md5(fullp.encode('utf-8')).hexdigest()
                        if iconkey2 not in custom_icons:
                            try:
                                custom_icons.load(iconkey2, fullp, 'IMAGE')
                            except:
                                pass
                        pi.preview_image   = iconkey2
                        pi.preview_filepath= fullp

    # Final recursive scan for the main stroke browser
    for main_item in props.stroke_type_folders:
        scan_directory_recursive(main_item.path, props.stroke_folders)
    print("[Painterly] scan_painterly_folders → completed")

# ----- NEW ICON RELOAD CODE END -----


def _mirror_path_to_scene(prefs, context):
    """
    Runs whenever prefs.base_folder_path changes.
    Mirrors the value to the scene and forces a rescan.
    """
    try:
        scn = context.scene
        if not scn:
            return
        props = scn.painterly_folder_properties
        props.base_path = prefs.base_folder_path
        props.folder_configured = bool(prefs.base_folder_path)
        scan_painterly_folders(context)
    except Exception as exc:
        print("[Painterly] mirror_path_to_scene failed:", exc)

class PAINTERLY_OT_install_dependencies(Operator):
    bl_idname = "painterly.install_dependencies"
    bl_label  = "Install Dependencies (PIL)"

    def execute(self, context):
        try:
            subprocess.check_call([sys.executable, "-m", "ensurepip", "--default-pip"])
            cmd = [sys.executable, "-m", "pip", "install"]
            if platform.system() == "Windows":
                cmd += ["--user"]
            cmd += ["Pillow"]
            subprocess.check_call(cmd)

            import site
            user_site = site.getusersitepackages()
            if user_site not in sys.path:
                sys.path.append(user_site)
            importlib.invalidate_caches()
            import PIL
            addon = context.preferences.addons.get(get_addon_key())
            if addon:
                addon.preferences.dependencies_installed = True
            self.report({'INFO'}, "Pillow installed successfully!")
            return {'FINISHED'}
        except Exception as e:
            self.report({'ERROR'}, f"Installation failed: {e}")
            return {'CANCELLED'}


class PAINTERLY_OT_save_preferences(Operator):
    bl_idname = "painterly.save_preferences"
    bl_label  = "Save Preferences"

    def execute(self, context):
        bpy.ops.wm.save_userpref()
        self.report({'INFO'}, "Preferences saved.")
        return {'FINISHED'}


class PAINTERLY_OT_open_feedback(Operator):
    bl_idname = "painterly.open_feedback"
    bl_label  = "Open Feedback Page"

    def execute(self, context):
        bpy.ops.wm.url_open(url="https://www.doughyanimation.com/contact")
        return {'FINISHED'}


class PAINTERLY_OT_open_youtube(Operator):
    bl_idname = "painterly.open_youtube"
    bl_label  = "Open YouTube Channel"

    def execute(self, context):
        bpy.ops.wm.url_open(url="https://www.youtube.com/@doughyanimation")
        return {'FINISHED'}

class PainterlyAddonPreferences(AddonPreferences):
    bl_idname = get_addon_key()

    # stored prefs
    base_folder_path: StringProperty(
        name="Base Folder Path",
        subtype='DIR_PATH',
        description="Folder that holds all Painterly assets",
        update=lambda self, ctx: _mirror_path_to_scene(self, ctx)
    )
    dependencies_installed: BoolProperty(name="Dependencies Installed", default=False)
    enable_auto_update:     BoolProperty(name="Enable Automatic Updates", default=True)

    # ---- UI -------------------------------------------------------------
    def draw(self, context):
        layout = self.layout
        props = context.scene.addon_properties # for updater status
        col = layout.column(align=True)

        # ─────────────── Base folder selector ───────────────
        col.prop(self, "base_folder_path")
        if self.base_folder_path:
            col.label(text="Folder set and saved ✔", icon='CHECKMARK')
        else:
            col.label(text="Not set – Painterly UI is hidden ⛔", icon='ERROR')
        col.operator("painterly.save_preferences", icon='FILE_TICK')

        # ─────────────── Dependencies (Pillow / PIL) ────────
        if check_pillow():
            col.label(text="PIL (Pillow) is installed ✔", icon='CHECKMARK')
        else:
            col.operator("painterly.install_dependencies", icon='IMPORT')

        # ─────────────── Auto-update toggle ─────────────────
        box = col.box()
        box.label(text="Automatic Updater", icon='FILE_REFRESH')
        box.prop(self, "enable_auto_update", text="Enable Auto Updates", toggle=True)
        if self.enable_auto_update:
            if not props.update_checked:
                box.operator("painterly.check_for_updates", text="Check for Updates")
            else:
                if props.update_available and not props.update_downloaded:
                    box.label(text=f"New Version: {props.latest_version}", icon='INFO')
                    box.label(text=props.latest_changelog)
                    box.operator("painterly.download_update", text="Update Available!", icon='IMPORT')
                elif props.update_downloaded:
                    box.label(text="Update Downloaded! Please restart Blender.", icon='INFO')
                    box.operator("painterly.restart_blender", text="Restart Blender", icon='RECOVER_LAST')
                else:
                    box.label(text="No Updates Available", icon='CHECKMARK')
                    box.operator("painterly.check_for_updates", text="Check Again")

        # ─────────────── Misc links ─────────────────────────
        row = col.row(align=True)
        row.operator("painterly.open_feedback", icon='HELP')
        row.operator("painterly.open_youtube",  icon='URL')


# ----- NEW COLOR MIXER CODE START -----

def schedule_inactive_ramp_updates(context):
    """Start / keep alive the timer that refreshes hidden ramps."""
    bpy.app.timers.register(
        debounce_update_inactive_ramp_nodes,
        first_interval=DEBOUNCE_INTERVAL
    )

def debounce_update_inactive_ramp_nodes():
    global last_color_update_time, pending_inactive_ramps
    try:
        if bpy.context.scene is None:
            return DEBOUNCE_INTERVAL

        if time.time() - last_color_update_time < DEBOUNCE_TOTAL_DELAY:
            return DEBOUNCE_INTERVAL

        if pending_inactive_ramps:
            node = pending_inactive_ramps.pop(0)
            update_ramp_node(node)
    except Exception as e:
        print("Error in debounce_update_inactive_ramp_nodes:", e)

    return DEBOUNCE_INTERVAL

def update_ramp_node(node):
    """
    Rebuilds *all* colour stops of the given ColorRamp node to reflect
    the current StrokeBrushProperties.
    """
    props = bpy.context.scene.stroke_brush_properties

    while len(node.color_ramp.elements) > 1:
        node.color_ramp.elements.remove(node.color_ramp.elements[-1])

    node.color_ramp.elements[0].color = props.color

    sec_list  = []
    if props.use_secondary_color:
        sec_list.append(props.secondary_color)
        sec_list.extend([ac.color for ac in props.additional_secondary_colors])

    base_list  = [ac.color for ac in props.additional_base_colors]
    final_list = base_list + sec_list

    for _ in final_list:
        node.color_ramp.elements.new(1.0)

    n_total = len(node.color_ramp.elements)
    if n_total > 1:
        for i, el in enumerate(node.color_ramp.elements):
            el.position = max(
                0.0,
                min(
                    ((i / (n_total - 1)) ** props.color_mixer)
                    + props.color_mixer_offset,
                    1.0
                )
            )

    node.color_ramp.elements[0].color = props.color
    idx = 1
    for col in final_list:
        node.color_ramp.elements[idx].color = col
        idx += 1

def update_color(context):
    """
    Kick-off routine that updates the *active* ramp immediately and
    queues all *inactive* ramps for deferred update (debounced).
    """
    global _in_update_color, last_color_update_time, pending_inactive_ramps
    last_color_update_time = time.time()
    props = context.scene.stroke_brush_properties

    if props.animation_mode == 'STATIC':
        update_active_color_ramp(context)
        return

    if _in_update_color:
        return

    _in_update_color = True
    try:
        update_active_color_ramp(context)
        pending_inactive_ramps = []
        obj = context.object
        if obj and obj.type == 'CURVE' and obj.data.materials:
            mat = obj.data.materials[0]
            fc = mat.get("frame_count", None)
            active_index = None
            if fc and fc > 0:
                step = props.step_value
                frame = context.scene.frame_current
                active_index = (int(((frame - 1) / step)) % fc) + 1
            
            for node in mat.node_tree.nodes:
                if node.type == 'VALTORGB' and node.name.startswith("StrokeColorRamp_"):
                    try:
                        node_index = int(node.name.split("_")[1])
                        if node_index != active_index:
                            pending_inactive_ramps.append(node)
                    except (ValueError, IndexError):
                        continue
        
        schedule_inactive_ramp_updates(context)
    finally:
        _in_update_color = False

# ----- NEW COLOR MIXER CODE END -----

@persistent
def painterly_frame_change_post(scene, depsgraph):
    pass

# ---------------------------
# Extras Update (Only optimized viewport is automatically updated)
# ---------------------------
def update_extras_strokes(context):
    stroke_props = context.scene.stroke_brush_properties
    for obj in bpy.data.objects:
        if obj.type == 'CURVE' and obj.name.startswith("Painterly_"):
            if stroke_props.optimized_viewport_strokes:
                obj.data.resolution_u = 3
                obj.data.render_resolution_u = 12
            else:
                obj.data.resolution_u = 12
                obj.data.render_resolution_u = 12

# ---------------------------
# Other Operators
# ---------------------------
class OpenAddonPreferencesOperator(Operator):
    bl_idname = "painterly.open_addon_preferences"
    bl_label = "Add-on Preferences"
    def execute(self, context):
        bpy.ops.screen.userpref_show('INVOKE_DEFAULT')
        context.preferences.active_section = 'ADDONS'
        return {'FINISHED'}

class SetCyclesRenderSettings(Operator):
    bl_idname = "painterly.set_cycles_render_settings"
    bl_label = "Cycles Render Settings"
    def execute(self, context):
        scn = context.scene
        scn.render.engine = 'CYCLES'
        if hasattr(scn.cycles, 'transparent_max_bounces'):
            scn.cycles.transparent_max_bounces = 256
        self.report({'INFO'}, "Render Settings: Transparent = 256")
        return {'FINISHED'}

def update_additional_color(self, context):
    update_color(context)

class AdditionalColor(PropertyGroup):
    color: FloatVectorProperty(
        name="Extra Color",
        subtype='COLOR',
        size=4,
        default=(1, 1, 1, 1),
        min=0.0,
        max=1.0,
        update=update_additional_color
    )

class PAINTERLY_OT_AddAdditionalColorSecondary(Operator):
    bl_idname = "painterly.add_additional_color_secondary"
    bl_label = "Add Additional Secondary Color"
    def execute(self, context):
        stroke_props = context.scene.stroke_brush_properties
        new_color = stroke_props.additional_secondary_colors.add()
        new_color.color = (1, 1, 1, 1)
        update_color(context)
        return {'FINISHED'}

class PAINTERLY_OT_RemoveAdditionalColorSecondary(Operator):
    bl_idname = "painterly.remove_additional_color_secondary"
    bl_label = "Remove Secondary Color"
    index: IntProperty()
    def execute(self, context):
        stroke_props = context.scene.stroke_brush_properties
        if 0 <= self.index < len(stroke_props.additional_secondary_colors):
            stroke_props.additional_secondary_colors.remove(self.index)
        update_color(context)
        return {'FINISHED'}

# ---------------------------
# Folder Item & Folder Properties
# ---------------------------
class FolderItem(PropertyGroup):
    name: StringProperty()
    path: StringProperty()
    preview_image: StringProperty()
    preview_filepath: StringProperty()
    category: StringProperty()

def get_main_folder_items(self, context):
    items = [("ALL", "ALL", "Gather from all folders")]
    if self.stroke_type_folders:
        for i, folder in enumerate(self.stroke_type_folders):
            items.append((str(i), folder.name, f"Select {folder.name} category"))
    if len(items) == 1:
        items = [('0', "No Categories", "No categories available")]
    return items

def get_subfolder_items(self, context):
    if self.selected_stroke_type == "ALL":
        return [("NA", "N/A", "Not applicable, main=ALL")]
    if not self.stroke_subtype_folders:
        return [('0', 'No Subfolders', 'No subfolders available')]
    items = [("ALL", "ALL", "All subfolders")]
    for i, f in enumerate(self.stroke_subtype_folders):
        items.append((str(i), f.name, f"Select {f.name}"))
    return items

class PainterlyFolderProperties(PropertyGroup):
    # This class is now a scene-side proxy. The master path is in AddonPreferences.
    base_path: StringProperty(default="")
    folder_configured: BoolProperty(default=False)
    
    stroke_type_folders: CollectionProperty(type=FolderItem)
    stroke_subtype_folders: CollectionProperty(type=FolderItem)
    stroke_folders: CollectionProperty(type=FolderItem)
    normal_map_folders: CollectionProperty(type=FolderItem)
    preset_folders: CollectionProperty(type=FolderItem)
    selected_stroke_type: EnumProperty(
        name="Main Folder",
        items=get_main_folder_items,
        update=lambda self, context: self.update_main_folder(context)
    )
    selected_stroke_subtype: EnumProperty(
        name="Subfolder",
        items=get_subfolder_items,
        update=lambda self, context: self.update_subfolder(context)
    )
    current_stroke_index: IntProperty(default=0)
    current_normal_map_index: IntProperty(default=0)
    current_preset_index: IntProperty(default=0)
    show_stroke_grid: BoolProperty(default=False)
    show_normal_grid: BoolProperty(default=False)
    show_preset_grid: BoolProperty(default=False)
    previews_per_page: IntProperty(default=4, min=2, max=9)
    def update_main_folder(self, context):
        self.stroke_subtype_folders.clear()
        self.stroke_folders.clear()
        if self.selected_stroke_type == "ALL":
            for main_item in self.stroke_type_folders:
                scan_directory_recursive(main_item.path, self.stroke_folders)
            self.selected_stroke_subtype = "NA"
        else:
            try:
                idx = int(self.selected_stroke_type)
            except:
                return
            if idx < 0 or idx >= len(self.stroke_type_folders):
                return
            main_folder = self.stroke_type_folders[idx]
            for sub_name in os.listdir(main_folder.path):
                sub_path = os.path.join(main_folder.path, sub_name)
                if os.path.isdir(sub_path) and sub_name.lower() != "ui_image":
                    it = self.stroke_subtype_folders.add()
                    it.name = sub_name
                    it.path = sub_path
                    it.category = sub_name
            self.selected_stroke_subtype = "ALL"
            self.update_subfolder(context)
        self.current_stroke_index = 0
    def update_subfolder(self, context):
        if self.selected_stroke_type == "ALL":
            return
        self.stroke_folders.clear()
        try:
            main_idx = int(self.selected_stroke_type)
        except:
            return
        if main_idx < 0 or main_idx >= len(self.stroke_type_folders):
            return
        if self.selected_stroke_subtype == "ALL":
            for sf_item in self.stroke_subtype_folders:
                scan_directory_recursive(sf_item.path, self.stroke_folders)
        else:
            try:
                sub_idx = int(self.selected_stroke_subtype)
            except:
                return
            if sub_idx < 0 or sub_idx >= len(self.stroke_subtype_folders):
                return
            chosen_sub = self.stroke_subtype_folders[sub_idx]
            scan_directory_recursive(chosen_sub.path, self.stroke_folders)
        self.current_stroke_index = 0

# ---------------------------
# GEOMETRY NODE MODE - HELPER FUNCTIONS (Blender 4.0+)
# ---------------------------
def get_geo_node_modifier(obj):
    """Finds the Painterly Geometry Nodes modifier on an object."""
    if not obj:
        return None
    for mod in obj.modifiers:
        if mod.type == 'NODES' and mod.node_group and mod.node_group.name.startswith("Painterly_GN_"):
            return mod
    return None

def create_painterly_geo_nodes_group(context, primary_stroke_object):
    """
    Creates the specific Geometry Nodes setup for Blender 4.0+.
    This now creates a base tree that instance branches will be added to.
    """
    base_name = f"Painterly_GN_{primary_stroke_object.name}"
    ng = bpy.data.node_groups.new(name=base_name, type="GeometryNodeTree")

    interface = ng.interface
    interface.new_socket(name="Geometry", in_out="INPUT", socket_type='NodeSocketGeometry')
    interface.new_socket(name="Geometry", in_out="OUTPUT", socket_type='NodeSocketGeometry')

    n_in = ng.nodes.new("NodeGroupInput")
    n_in.name = "Group Input" # Keep default name for easier lookup
    n_in.location = (-300, 0)
    
    n_out = ng.nodes.new("NodeGroupOutput")
    n_out.location = (600, 0)
    
    n_setmat = ng.nodes.new("GeometryNodeSetMaterial")
    n_setmat.location = (0, -150)
    if primary_stroke_object.active_material:
        n_setmat.inputs["Material"].default_value = primary_stroke_object.active_material
    
    n_join = ng.nodes.new("GeometryNodeJoinGeometry")
    n_join.name = "Painterly_Join"
    n_join.location = (300, 0)

    # Link up the base mesh pass-through
    ng.links.new(n_in.outputs["Geometry"], n_setmat.inputs["Geometry"])
    ng.links.new(n_setmat.outputs["Geometry"], n_join.inputs[0])
    ng.links.new(n_join.outputs["Geometry"], n_out.inputs["Geometry"])

    # Add the modifier to the object
    mod = primary_stroke_object.modifiers.new(name="Painterly Geo Nodes", type='NODES')
    mod.node_group = ng
    
    return mod

# ---------------------------
# GEOMETRY NODE MODE - PROPERTY GROUPS & CALLBACKS (Blender 4.0+)
# ---------------------------
def get_primary_stroke_collections(self, context):
    """Dynamically generates a list of primary stroke objects for the dropdown."""
    items = []
    geo_props = context.scene.geo_node_properties
    if not geo_props.primary_strokes:
        return [("NONE", "No Primary Strokes", "Create a Primary Stroke first")]
        
    for i, ps in enumerate(geo_props.primary_strokes):
        if ps.obj:
            items.append((str(i), ps.obj.name, f"Instance to '{ps.obj.name}'"))
    return items

def update_geo_node_instance_values(self, context):
    """Directly updates the values of named nodes within a specific instance branch."""
    primary_stroke = None
    secondary_stroke_prop = None
    for ps in context.scene.geo_node_properties.primary_strokes:
        for ss in ps.secondary_strokes:
            if ss.as_pointer() == self.as_pointer():
                primary_stroke = ps
                secondary_stroke_prop = ss
                break
        if primary_stroke:
            break
            
    if not primary_stroke or not primary_stroke.obj:
        return

    mod = get_geo_node_modifier(primary_stroke.obj)
    if not mod or not mod.node_group:
        return
        
    nodes = mod.node_group.nodes
    
    if not secondary_stroke_prop.obj: return

    secondary_name = re.sub(r'[^\w\s-]', '', secondary_stroke_prop.obj.name).replace(' ', '_')
    
    dist_node = nodes.get(f"Distribute_{secondary_name}")
    scale_node = nodes.get(f"Scale_{secondary_name}")
    rot_node = nodes.get(f"Rotation_{secondary_name}")
    merge_node = nodes.get(f"Merge_{secondary_name}")
    transform_node = nodes.get(f"Transform_{secondary_name}")
    align_rot_node = nodes.get(f"AlignRotation_{secondary_name}")
    switch_node = nodes.get(f"SwitchRotation_{secondary_name}")

    if dist_node: dist_node.inputs["Density"].default_value = self.density
    if scale_node: scale_node.inputs["Max"].default_value = self.scale
    if rot_node: rot_node.inputs["Max"].default_value = (self.rotation_randomness * math.pi * 2, self.rotation_randomness * math.pi * 2, self.rotation_randomness * math.pi * 2)
    if merge_node: merge_node.inputs["Distance"].default_value = self.merge_distance
    
    if transform_node:
        transform_node.inputs['Translation'].default_value = self.translation
        # The 'rotation' property is already in radians because its subtype is 'EULER'.
        # No extra conversion is needed.
        transform_node.inputs['Rotation'].default_value = self.rotation
        transform_node.inputs['Scale'].default_value = self.scale_transform

    if align_rot_node:
        if hasattr(align_rot_node, 'rotation_type'):  # Blender 4.1+
            align_rot_node.rotation_type = self.align_axis + '_AXIS'
        elif hasattr(align_rot_node, 'axis'): # Blender 4.0
            align_rot_node.axis = self.align_axis
        
    if switch_node:
        switch_node.inputs['Switch'].default_value = self.use_align_rotation

    return None

class GeoNodeSecondaryStroke(PropertyGroup):
    """Properties for a single secondary (instanced) stroke."""
    name: StringProperty(name="Name")
    obj: PointerProperty(type=bpy.types.Object, name="Secondary Stroke Object")
    
    density: FloatProperty(name="Density", default=0.1, min=0.0, max=1000.0, update=update_geo_node_instance_values, step=10)
    scale: FloatProperty(name="Scale", description="Controls the maximum random scale of instances", default=1.0, min=0.0, max=50.0, update=update_geo_node_instance_values, step=1)
    rotation_randomness: FloatProperty(name="Rotation", default=1.0, min=0.0, max=1.0, update=update_geo_node_instance_values, description="Controls the maximum random rotation on all axes")
    merge_distance: FloatProperty(name="Merge Distance", default=0.0, min=0.0, max=10.0, update=update_geo_node_instance_values, step=1, precision=3)

    align_rotation_available: BoolProperty(name="Align Rotation Available", default=True)
    use_align_rotation: BoolProperty(name="Align Rotation to Vector", default=False, update=update_geo_node_instance_values)
    align_axis: EnumProperty(name="Axis", items=[('X', "X", ""), ('Y', "Y", ""), ('Z', "Z", "")], default='Z', update=update_geo_node_instance_values)

    use_edit_transforms: BoolProperty(name="Edit Transforms", default=False)
    translation: FloatVectorProperty(name="Translation", subtype='TRANSLATION', size=3, update=update_geo_node_instance_values)
    rotation: FloatVectorProperty(name="Rotation", subtype='EULER', size=3, unit='ROTATION', update=update_geo_node_instance_values)
    scale_transform: FloatVectorProperty(name="Scale", subtype='XYZ', size=3, default=(1.0, 1.0, 1.0), update=update_geo_node_instance_values)

class GeoNodePrimaryStroke(PropertyGroup):
    """Properties for a single primary stroke setup."""
    name: StringProperty(name="Name")
    obj: PointerProperty(type=bpy.types.Object, name="Primary Stroke Object")
    secondary_strokes: CollectionProperty(type=GeoNodeSecondaryStroke)


class GeoNodeProperties(PropertyGroup):
    """Main property group for the Geometry Node Mode."""
    geo_node_mode_enabled: BoolProperty(
        name="Geometry Node Mode",
        description="Enable to access Geometry Node tools for strokes (Blender 4.0+)",
        default=False
    )
    primary_strokes: CollectionProperty(type=GeoNodePrimaryStroke)
    
    target_primary_collection: EnumProperty(
        name="Target Object",
        description="Choose which Primary Stroke object to instance this object to",
        items=get_primary_stroke_collections
    )

# ---------------------------
# GEOMETRY NODE MODE - OPERATORS (Blender 4.0+)
# ---------------------------
class PAINTERLY_OT_AddPrimaryStroke(Operator):
    bl_idname = "painterly.add_primary_stroke"
    bl_label = "Add Primary Stroke"
    bl_description = "Make the active object a new Primary Stroke, creating a Geometry Node setup"
    bl_options = {'REGISTER', 'UNDO'}

    @classmethod
    def poll(cls, context):
        return context.active_object and context.active_object.type in {'CURVE', 'MESH'}

    def execute(self, context):
        geo_props = context.scene.geo_node_properties
        obj = context.active_object

        for ps in geo_props.primary_strokes:
            if ps.obj == obj:
                self.report({'WARNING'}, f"Object '{obj.name}' is already a Primary Stroke.")
                return {'CANCELLED'}
        
        new_primary = geo_props.primary_strokes.add()
        new_primary.name = obj.name
        new_primary.obj = obj
        
        create_painterly_geo_nodes_group(context, obj)

        new_index = len(geo_props.primary_strokes) - 1
        geo_props.target_primary_collection = str(new_index)
        
        self.report({'INFO'}, f"Added '{obj.name}' as a new Primary Stroke.")
        return {'FINISHED'}

class PAINTERLY_OT_InstanceStroke(Operator):
    bl_idname = "painterly.instance_stroke"
    bl_label = "Instance Selected to Target"
    bl_description = "Add selected objects as new instances on the target Primary Stroke"
    bl_options = {'REGISTER', 'UNDO'}

    @classmethod
    def poll(cls, context):
        geo_props = context.scene.geo_node_properties
        return context.selected_objects and len(geo_props.primary_strokes) > 0

    def execute(self, context):
        geo_props = context.scene.geo_node_properties
        if not geo_props.target_primary_collection or geo_props.target_primary_collection == 'NONE':
            self.report({'ERROR'}, "No target Primary Stroke selected.")
            return {'CANCELLED'}
            
        target_idx = int(geo_props.target_primary_collection)
        primary_stroke_target = geo_props.primary_strokes[target_idx]
        primary_obj = primary_stroke_target.obj
        
        if not primary_obj:
            self.report({'ERROR'}, "Target Primary Stroke object not found.")
            return {'CANCELLED'}

        mod = get_geo_node_modifier(primary_obj)
        if not mod or not mod.node_group:
            self.report({'ERROR'}, f"No valid Painterly GN modifier on '{primary_obj.name}'.")
            return {'CANCELLED'}
        
        ng = mod.node_group
        nodes = ng.nodes
        links = ng.links
        
        n_join = nodes.get("Painterly_Join")
        n_in = nodes.get("Group Input")
        if not n_join or not n_in:
            self.report({'ERROR'}, "Base node tree is corrupted. Please remove and re-add Primary Stroke.")
            return {'CANCELLED'}

        added_count = 0
        for secondary_obj in context.selected_objects:
            if primary_obj == secondary_obj: continue
            if any(ps.obj == secondary_obj for ps in geo_props.primary_strokes): continue
            if any(ss.obj == secondary_obj for ss in primary_stroke_target.secondary_strokes): continue
            
            ss_prop = primary_stroke_target.secondary_strokes.add()
            ss_prop.name = secondary_obj.name
            ss_prop.obj = secondary_obj

            secondary_name = re.sub(r'[^\w\s-]', '', secondary_obj.name).replace(' ', '_')
            y_pos = -450 * (len(primary_stroke_target.secondary_strokes))
            
            n_dist = nodes.new("GeometryNodeDistributePointsOnFaces")
            n_dist.name = f"Distribute_{secondary_name}"; n_dist.location = (-50, y_pos)
            n_dist.distribute_method = 'RANDOM'

            n_obj_info = nodes.new("GeometryNodeObjectInfo")
            n_obj_info.name = f"ObjInfo_{secondary_name}"; n_obj_info.location = (200, y_pos + 150)
            n_obj_info.inputs['Object'].default_value = secondary_obj
            
            n_rand_scale = nodes.new("FunctionNodeRandomValue")
            n_rand_scale.name = f"Scale_{secondary_name}"; n_rand_scale.location = (200, y_pos - 50)
            n_rand_scale.data_type = 'FLOAT'
            n_rand_scale.inputs["Min"].default_value = 0.0

            n_rand_rot = nodes.new("FunctionNodeRandomValue")
            n_rand_rot.name = f"Rotation_{secondary_name}"; n_rand_rot.location = (200, y_pos - 200)
            n_rand_rot.data_type = 'FLOAT_VECTOR'
            n_rand_rot.inputs["Min"].default_value = (0,0,0)
            
            n_instance = nodes.new("GeometryNodeInstanceOnPoints")
            n_instance.name = f"Instance_{secondary_name}"; n_instance.location = (950, y_pos)
            
            n_merge = nodes.new("GeometryNodeMergeByDistance")
            n_merge.name = f"Merge_{secondary_name}"; n_merge.location = (1200, y_pos)
            
            n_transform = nodes.new("GeometryNodeTransform")
            n_transform.name = f"Transform_{secondary_name}"; n_transform.location = (1450, y_pos)

            n_align_rot = None
            # This block attempts to create the rotation alignment node,
            # trying the Blender 4.1+ name first, then falling back to the 4.0 name.
            try:
                # Try the node name for Blender 4.1+
                n_align_rot = nodes.new("GeometryNodeVectorToRotation")
            except RuntimeError:
                try:
                    # If the first attempt fails, try the older node name for Blender 4.0
                    n_align_rot = nodes.new("FunctionNodeAlignRotationToVector")
                except RuntimeError:
                    # If both names fail, the node is not available.
                    n_align_rot = None

            if n_align_rot:
                # If the node was created successfully with either name, configure it.
                n_align_rot.name = f"AlignRotation_{secondary_name}"
                n_align_rot.location = (450, y_pos - 350)
                ss_prop.align_rotation_available = True
            else:
                # If the node could not be created, disable the feature and warn the user.
                ss_prop.align_rotation_available = False
                self.report({'WARNING'}, "'Vector to Rotation' node not found. Alignment feature disabled.")

            links.new(n_in.outputs["Geometry"], n_dist.inputs["Mesh"])
            links.new(n_dist.outputs["Points"], n_instance.inputs["Points"])
            links.new(n_obj_info.outputs["Geometry"], n_instance.inputs["Instance"])
            links.new(n_rand_scale.outputs["Value"], n_instance.inputs["Scale"])
            links.new(n_instance.outputs["Instances"], n_merge.inputs["Geometry"])
            links.new(n_merge.outputs["Geometry"], n_transform.inputs["Geometry"])
            links.new(n_transform.outputs["Geometry"], n_join.inputs[0])

            if n_align_rot:
                n_switch = nodes.new("GeometryNodeSwitch")
                n_switch.name = f"SwitchRotation_{secondary_name}"
                n_switch.location = (700, y_pos - 200)
                n_switch.input_type = 'ROTATION'
                
                # Use named sockets instead of indices
                links.new(n_rand_rot.outputs["Value"], n_switch.inputs['False'])
                links.new(n_align_rot.outputs['Rotation'], n_switch.inputs['True'])
                links.new(n_dist.outputs['Normal'], n_align_rot.inputs['Vector'])
                links.new(n_switch.outputs['Output'], n_instance.inputs['Rotation'])
            else:
                # Fallback to only random rotation if alignment node is not available
                links.new(n_rand_rot.outputs["Value"], n_instance.inputs['Rotation'])

            update_geo_node_instance_values(ss_prop, context)
            
            secondary_obj.hide_set(True)
            secondary_obj.hide_render = True
            added_count += 1
        
        if added_count > 0:
            self.report({'INFO'}, f"Instanced {added_count} object(s) to '{primary_obj.name}'.")
        else:
            self.report({'INFO'}, "No new objects were instanced.")

        return {'FINISHED'}


class PAINTERLY_OT_RemovePrimaryStroke(Operator):
    bl_idname = "painterly.remove_primary_stroke"
    bl_label = "Remove Primary Stroke"
    bl_description = "Remove the Primary Stroke, its modifier, and un-instance all secondary strokes"
    bl_options = {'REGISTER', 'UNDO'}

    primary_stroke_index: IntProperty()

    def execute(self, context):
        geo_props = context.scene.geo_node_properties
        if self.primary_stroke_index >= len(geo_props.primary_strokes):
            return {'CANCELLED'}
            
        primary_to_remove = geo_props.primary_strokes[self.primary_stroke_index]
        obj = primary_to_remove.obj

        # Make secondary strokes visible again
        for ss in primary_to_remove.secondary_strokes:
            if ss.obj:
                ss.obj.hide_set(False)
                ss.obj.hide_render = False

        if obj:
            mod = get_geo_node_modifier(obj)
            if mod:
                ng = mod.node_group
                obj.modifiers.remove(mod)
                if ng and ng.users == 0:
                    bpy.data.node_groups.remove(ng)
        
        geo_props.primary_strokes.remove(self.primary_stroke_index)
        
        self.report({'INFO'}, f"Removed Primary Stroke '{primary_to_remove.name}'.")
        return {'FINISHED'}

class PAINTERLY_OT_RemoveSecondaryStroke(Operator):
    bl_idname = "painterly.remove_secondary_stroke"
    bl_label = "Remove Secondary Stroke Instance"
    bl_description = "Remove the object instance from the Primary Stroke"
    bl_options = {'REGISTER', 'UNDO'}

    primary_stroke_index: IntProperty()
    secondary_stroke_index: IntProperty()

    def execute(self, context):
        geo_props = context.scene.geo_node_properties
        primary_stroke = geo_props.primary_strokes[self.primary_stroke_index]
        secondary_stroke = primary_stroke.secondary_strokes[self.secondary_stroke_index]
        primary_obj = primary_stroke.obj
        secondary_obj = secondary_stroke.obj

        if not primary_obj or not secondary_obj:
            return {'CANCELLED'}

        # Remove nodes from GN tree
        mod = get_geo_node_modifier(primary_obj)
        if mod and mod.node_group:
            ng = mod.node_group
            secondary_name = re.sub(r'[^\w\s-]', '', secondary_obj.name).replace(' ', '_')
            
            nodes_to_remove = []
            for node in ng.nodes:
                if node.name.endswith(f"_{secondary_name}"):
                    nodes_to_remove.append(node)
            
            for node in nodes_to_remove:
                ng.nodes.remove(node)

        # Unhide the object
        secondary_obj.hide_set(False)
        secondary_obj.hide_render = False
        
        # Remove from property group
        primary_stroke.secondary_strokes.remove(self.secondary_stroke_index)

        self.report({'INFO'}, f"Removed instance '{secondary_obj.name}' from '{primary_obj.name}'.")
        return {'FINISHED'}
        
class PAINTERLY_OT_SelectObject(Operator):
    bl_idname = "painterly.select_object"
    bl_label = "Select and Show Object"
    bl_description = "Make this object visible and select it in the 3D View"
    bl_options = {'REGISTER', 'UNDO'}
    
    obj_name: StringProperty()
    
    def execute(self, context):
        obj = bpy.data.objects.get(self.obj_name)
        if not obj:
            self.report({'WARNING'}, f"Object '{self.obj_name}' not found.")
            return {'CANCELLED'}
        
        # Make the object visible before selecting
        obj.hide_set(False)
        obj.hide_render = False
            
        bpy.ops.object.select_all(action='DESELECT')
        obj.select_set(True)
        context.view_layer.objects.active = obj
        return {'FINISHED'}

class PAINTERLY_OT_ToggleInstanceVisibility(Operator):
    bl_idname = "painterly.toggle_instance_visibility"
    bl_label = "Toggle Instance Visibility"
    bl_description = "Toggle viewport and render visibility for this instance"
    bl_options = {'REGISTER', 'UNDO'}

    obj_name: StringProperty()

    def execute(self, context):
        obj = bpy.data.objects.get(self.obj_name)
        if not obj:
            self.report({'WARNING'}, f"Object '{self.obj_name}' not found.")
            return {'CANCELLED'}

        # Toggle visibility
        new_hide_state = not obj.hide_get()
        obj.hide_set(new_hide_state)
        obj.hide_render = new_hide_state

        if new_hide_state:
            self.report({'INFO'}, f"Hid instance '{obj.name}'.")
        else:
            self.report({'INFO'}, f"Made instance '{obj.name}' visible.")
            
        return {'FINISHED'}

EFFECT_NONE = "NONE"
EFFECT_MAGIC = "MAGIC"
EFFECT_VORONOI = "VORONOI"
EFFECT_NOISE = "NOISE"
EFFECT_TYPES = [
    (EFFECT_NONE, "None", "No effect"),
    (EFFECT_MAGIC, "Magic Texture", ""),
    (EFFECT_VORONOI, "Voronoi Texture", ""),
    (EFFECT_NOISE, "Noise Texture", ""),
]

def effect_update_callback(self, context):
    update_effect_nodes(context)

def update_effect_nodes(context):
    props = context.scene.stroke_brush_properties
    obj = context.object
    if not obj or obj.type != 'CURVE' or not obj.data.materials:
        return
    mat = obj.data.materials[0]
    if not mat or not mat.node_tree:
        return
    node_tree = mat.node_tree
    # Remove old effect nodes
    for nd in list(node_tree.nodes):
        if nd.name.startswith("PainterlyMagic") or nd.name.startswith("PainterlyVoronoi") or nd.name.startswith("PainterlyNoise"):
            node_tree.nodes.remove(nd)
    if props.effect_type == EFFECT_NONE:
        return
    # Ensure TEX_COORD and MAPPING nodes exist
    texcoord_node, mapping_node = None, None
    for nd in node_tree.nodes:
        if nd.type == 'TEX_COORD':
            texcoord_node = nd
        if nd.type == 'MAPPING':
            mapping_node = nd
    if not texcoord_node:
        texcoord_node = node_tree.nodes.new("ShaderNodeTexCoord")
    if not mapping_node:
        mapping_node = node_tree.nodes.new("ShaderNodeMapping")
    if not any(link.from_node == texcoord_node and link.to_node == mapping_node for link in node_tree.links):
        if "Generated" in texcoord_node.outputs:
            node_tree.links.new(texcoord_node.outputs["Generated"], mapping_node.inputs["Vector"])
    # Create the selected effect node
    effect_node = None
    if props.effect_type == EFFECT_MAGIC:
        node = node_tree.nodes.new("ShaderNodeTexMagic")
        node.name = "PainterlyMagic"
        if "Scale" in node.inputs:
            node.inputs["Scale"].default_value = props.effect_magic_scale
        if "Distortion" in node.inputs:
            node.inputs["Distortion"].default_value = props.effect_magic_distortion
        node.turbulence_depth = props.effect_magic_depth
        effect_node = node
    elif props.effect_type == EFFECT_VORONOI:
        node = node_tree.nodes.new("ShaderNodeTexVoronoi")
        node.name = "PainterlyVoronoi"
        if "Scale" in node.inputs:
            node.inputs["Scale"].default_value = props.effect_voronoi_scale
        if "Smoothness" in node.inputs:
            node.inputs["Smoothness"].default_value = props.effect_voronoi_smoothness
        if "Exponent" in node.inputs:
            node.inputs["Exponent"].default_value = props.effect_voronoi_exponent
        if "Randomness" in node.inputs:
            node.inputs["Randomness"].default_value = props.effect_voronoi_randomness
        node.feature = props.effect_voronoi_feature
        node.distance = props.effect_voronoi_distance
        effect_node = node
    elif props.effect_type == EFFECT_NOISE:
        node = node_tree.nodes.new("ShaderNodeTexNoise")
        node.name = "PainterlyNoise"
        if "Scale" in node.inputs:
            node.inputs["Scale"].default_value = props.effect_noise_scale
        if "Detail" in node.inputs:
            node.inputs["Detail"].default_value = props.effect_noise_detail
        if "Roughness" in node.inputs:
            node.inputs["Roughness"].default_value = props.effect_noise_roughness
        if "Distortion" in node.inputs:
            node.inputs["Distortion"].default_value = props.effect_noise_distortion
        effect_node = node
    if not effect_node:
        return
    # Connect the effect node to the mapping node
    node_tree.links.new(effect_node.inputs["Vector"], mapping_node.outputs["Vector"])
    # For each image texture node, use the helper function to set its "Vector" input
    for nd in node_tree.nodes:
        if nd.type == 'TEX_IMAGE' and (nd.name.startswith("StrokeFrame_") or nd.name.startswith("NormalFrame_")):
            if nd.name.startswith("StrokeFrame_"):
                connect_effect_output(node_tree, effect_node, nd, props.effect_color_vec_mode, props.effect_type)
            else:
                connect_effect_output(node_tree, effect_node, nd, props.effect_normal_vec_mode, props.effect_type)

def connect_effect_output(node_tree, effect_node, tex_node, mode, effect_type):
    if mode == "OFF":
        return
    if mode == "COLOR":
        out_name = "Color"
    elif mode == "FACPOS":
        if effect_type == EFFECT_VORONOI:
            out_name = "Distance"
        else:
            out_name = "Fac"
    else:
        return
    for ln in list(node_tree.links):
        if ln.to_node == tex_node and ln.to_socket.name == "Vector":
            node_tree.links.remove(ln)
    if out_name in effect_node.outputs and "Vector" in tex_node.inputs:
        node_tree.links.new(effect_node.outputs[out_name], tex_node.inputs["Vector"])

def update_active_color_ramp(context):
    props = context.scene.stroke_brush_properties
    obj = context.object
    if obj and obj.type == 'CURVE' and obj.data.materials:
        mat = obj.data.materials[0]
        fc = None
        try:
            fc = mat["frame_count"]
        except:
            fc = None
        if props.animation_mode == 'STATIC' or fc is None or fc <= 0:
            active_index = 1
        else:
            step = props.step_value
            frame = context.scene.frame_current
            active_index = (int(((frame - 1) / step)) % fc) + 1
        for node in mat.node_tree.nodes:
            if node.type == 'VALTORGB' and node.name.startswith("StrokeColorRamp_"):
                try:
                    node_index = int(node.name.split("_")[1])
                except:
                    continue
                if node_index == active_index:
                    update_ramp_node(node)

def update_inactive_color_ramps(context):
    global pending_inactive_ramps
    if pending_inactive_ramps:
        ramp_node = pending_inactive_ramps.pop(0)
        update_ramp_node(ramp_node)
    return None

def update_material_properties(context):
    props = context.scene.stroke_brush_properties
    obj = context.object
    if obj and obj.type == 'CURVE' and obj.data.materials:
        for mat in obj.data.materials:
            if mat and mat.node_tree:
                node_tree = mat.node_tree
                for node in node_tree.nodes:
                    if node.type == 'BSDF_PRINCIPLED' and node.name.startswith("StrokeBSDF_"):
                        try:
                            index = node.name.split("_")[1]
                        except:
                            pass
                        for link in list(node_tree.links):
                            if link.to_node == node and link.to_socket.name == "Base Color":
                                node_tree.links.remove(link)
                        for link in list(node_tree.links):
                            if link.to_node == node and link.to_socket.name in {"Emission", "Emission Color"}:
                                node_tree.links.remove(link)
                        ramp_node = None
                        if index:
                            ramp_node = node_tree.nodes.get(f"StrokeColorRamp_{index}")
                        if ramp_node and "Color" in ramp_node.outputs:
                            node_tree.links.new(ramp_node.outputs["Color"], node.inputs["Base Color"])
                            emission_socket = node.inputs.get("Emission") or node.inputs.get("Emission Color")
                            if emission_socket:
                                node_tree.links.new(ramp_node.outputs["Color"], emission_socket)
                        else:
                            node.inputs["Base Color"].default_value = props.color
                            if "Emission" in node.inputs:
                                node.inputs["Emission"].default_value = (props.color[0], props.color[1], props.color[2], 1)
                        node.inputs["Emission Strength"].default_value = props.emission
                        node.inputs["Metallic"].default_value = props.metallic
                        node.inputs["Roughness"].default_value = props.roughness
                        subsurface_socket = node.inputs.get("Subsurface") or node.inputs.get("Subsurface Weight")
                        if subsurface_socket:
                            for link in list(node_tree.links):
                                if link.to_node == node and link.to_socket.name in {"Subsurface", "Subsurface Weight"}:
                                    node_tree.links.remove(link)
                            subsurface_socket.default_value = props.subsurface_amount
                        if "Subsurface Radius" in node.inputs:
                            for link in list(node_tree.links):
                                if link.to_node == node and link.to_socket.name == "Subsurface Radius":
                                    node_tree.links.remove(link)
                            node.inputs["Subsurface Radius"].default_value = props.subsurface_radius
                        if "Subsurface Scale" in node.inputs:
                            for link in list(node_tree.links):
                                if link.to_node == node and link.to_socket.name == "Subsurface Scale":
                                    node_tree.links.remove(link)
                            node.inputs["Subsurface Scale"].default_value = props.subsurface_scale
                for node in node_tree.nodes:
                    if node.type == 'NORMAL_MAP' and "Normal Map" in node.name:
                        node.space = 'OBJECT'
                        node.inputs['Strength'].default_value = props.normal_map_strength
                try:
                    mat.use_sss_translucency = True
                    if hasattr(mat.cycles, 'sss_method'):
                        mat.cycles.sss_method = 'RANDOM_WALK'
                        mat.update_tag()
                except Exception as e:
                    print("Error setting subsurface method:", e)

def update_extrusion(context):
    props = context.scene.stroke_brush_properties
    obj = context.object
    if obj and obj.type == 'CURVE':
        if props.lock_depth_to_extrusion:
            obj.data.extrude = props.extrusion_locked
            obj.data.bevel_depth = props.extrusion_locked * 10.0
        else:
            obj.data.extrude = props.extrusion
            obj.data.bevel_depth = props.depth

def update_shrinkwrap_offset(context):
    props = context.scene.stroke_brush_properties
    obj = context.object
    if obj and obj.modifiers:
        sw = next((m for m in obj.modifiers if m.type == 'SHRINKWRAP'), None)
        if sw:
            sw.offset = props.shrinkwrap_offset

def update_displacement(context):
    props = context.scene.stroke_brush_properties
    obj = context.object
    if not obj or obj.type != 'CURVE' or not obj.data.materials:
        return
    mat = obj.data.materials[0]
    if not mat or not mat.node_tree:
        return
    disp = mat.node_tree.nodes.get("Displacement")
    if disp:
        disp.inputs["Height"].default_value = props.displacement_height
        disp.inputs["Midlevel"].default_value = props.displacement_midlevel
        disp.inputs["Scale"].default_value = props.displacement_scale

def update_solidify_modifier(self, context):
    obj = context.object
    if not obj or obj.type != 'CURVE':
        return

    mod_name = "Painterly_Solidify"
    mod = obj.modifiers.get(mod_name)
    
    if self.use_solidify:
        if not mod:
            mod = obj.modifiers.new(name=mod_name, type='SOLIDIFY')
        
        mod.thickness = self.solidify_thickness
        mod.offset = self.solidify_offset
    else:
        if mod:
            obj.modifiers.remove(mod)

# --- NEW: Wave Modifier Functions ---
def update_wave_values(self, context):
    obj = context.active_object
    if not obj: return
    mod = obj.modifiers.get("Painterly_Wave")
    if not mod: return
    
    props = context.scene.stroke_brush_properties
    mod.height = props.wave_height
    mod.width = props.wave_width
    mod.narrowness = props.wave_narrowness
    mod.speed = props.wave_speed
    mod.use_x = props.wave_motion_x
    mod.use_y = props.wave_motion_y

class PAINTERLY_OT_ToggleWaveModifier(Operator):
    bl_idname = "painterly.toggle_wave_modifier"
    bl_label = "Add/Remove Wave Modifier"
    bl_description = "Add or remove a Wave modifier to the active stroke"

    def execute(self, context):
        obj = context.active_object
        if not obj or obj.type != 'CURVE':
            self.report({'WARNING'}, "Active object must be a Painterly stroke.")
            return {'CANCELLED'}
        
        mod = obj.modifiers.get("Painterly_Wave")
        if mod:
            obj.modifiers.remove(mod)
            self.report({'INFO'}, "Wave modifier removed.")
        else:
            props = context.scene.stroke_brush_properties
            mod = obj.modifiers.new(name="Painterly_Wave", type='WAVE')
            mod.height = props.wave_height
            mod.width = props.wave_width
            mod.narrowness = props.wave_narrowness
            mod.speed = props.wave_speed
            mod.use_x = props.wave_motion_x
            mod.use_y = props.wave_motion_y
            self.report({'INFO'}, "Wave modifier added.")
        return {'FINISHED'}
# --- End Wave Modifier ---

def update_step_drivers(context):
    props = context.scene.stroke_brush_properties
    obj = context.object
    if obj and obj.data.materials:
        mat = obj.data.materials[0]
        if mat and mat.node_tree and mat.get("frame_count"):
            fc = mat["frame_count"]
            if not mat.node_tree.animation_data:
                return
            for node in mat.node_tree.nodes:
                if node.type == 'MIX_SHADER' and "Mix Shader" in node.name:
                    for fcurve in (mat.node_tree.animation_data.drivers if mat.node_tree.animation_data else []):
                        if fcurve.data_path == f'nodes["{node.name}"].inputs[0].default_value':
                            try:
                                index = int(node.name.split("_")[1])
                            except:
                                continue
                            
                            # --- ROBUST DRIVER EXPRESSION ---
                            fcurve.driver.expression = f"int(((frame - 1) / step)) % max(fc, 1) + 1 == {index}"
                            
                            driver = fcurve.driver
                            # Re-establish variables to be safe
                            vars = {v.name: v for v in driver.variables}
                            if "frame" not in vars:
                                vars["frame"] = driver.variables.new()
                                vars["frame"].name = "frame"
                            if "step" not in vars:
                                vars["step"] = driver.variables.new()
                                vars["step"].name = "step"
                            if "fc" not in vars:
                                vars["fc"] = driver.variables.new()
                                vars["fc"].name = "fc"
                            
                            vars["frame"].targets[0].id_type = 'SCENE'
                            vars["frame"].targets[0].id = context.scene
                            vars["frame"].targets[0].data_path = "frame_current"

                            vars["step"].targets[0].id_type = 'SCENE'
                            vars["step"].targets[0].id = context.scene
                            vars["step"].targets[0].data_path = "stroke_brush_properties.step_value"
                            
                            vars["fc"].targets[0].id_type = 'MATERIAL'
                            vars["fc"].targets[0].id = mat
                            vars["fc"].targets[0].data_path = '["frame_count"]'


def update_alpha_channel(context):
    props = context.scene.stroke_brush_properties
    obj = context.object
    if not obj or obj.type != 'CURVE' or not obj.data.materials:
        return
    mat = obj.data.materials[0]
    if not mat or not mat.node_tree:
        return
    node_tree = mat.node_tree
    for node in node_tree.nodes:
        if node.type == 'BSDF_PRINCIPLED' and node.name.startswith("StrokeBSDF_"):
            idx = node.name.split("_")[-1]
            img_node_name = f"StrokeFrame_{idx}"
            img_node = node_tree.nodes.get(img_node_name)
            alpha_socket = node.inputs["Alpha"]
            if props.use_alpha_channel:
                link_found = False
                for link in node_tree.links:
                    if link.to_node == node and link.to_socket == alpha_socket:
                        link_found = True
                        break
                if not link_found and img_node:
                    node_tree.links.new(img_node.outputs["Alpha"], alpha_socket)
            else:
                links_to_remove = []
                for link in node_tree.links:
                    if link.to_node == node and link.to_socket == alpha_socket:
                        links_to_remove.append(link)
                for lnk in links_to_remove:
                    node_tree.links.remove(lnk)

# ---------------------------
# Tilt Control Integration (DEFINED BEFORE USAGE)
# ---------------------------
def update_global_tilt(self, context):
    props = context.scene.stroke_brush_properties
    obj = context.object
    if obj and obj.type == 'CURVE':
        for spline in obj.data.splines:
            if hasattr(spline, "bezier_points"):
                for pt in spline.bezier_points:
                    pt.tilt = props.global_tilt

def apply_mean_tilt(context):
    props = context.scene.stroke_brush_properties
    obj = context.object
    if obj and obj.type == 'CURVE' and obj.mode == 'EDIT':
        for spline in obj.data.splines:
            if hasattr(spline, "bezier_points"):
                for point in spline.bezier_points:
                    if point.select_control_point:
                        point.tilt = props.mean_tilt

class StartMaintainingTiltOperator(Operator):
    """Continuously enforces Mean Tilt while selected points remain active"""
    bl_idname = "object.start_maintaining_tilt"
    bl_label  = "Start Maintaining Tilt"
    _timer = None

    def modal(self, context, event):
        if event.type == 'TIMER':
            apply_mean_tilt(context)

        if not context.scene.stroke_brush_properties.maintain_tilt:
            self.cancel(context)
            return {'CANCELLED'}

        return {'PASS_THROUGH'}

    def execute(self, context):
        wm = context.window_manager
        self._timer = wm.event_timer_add(0.1, window=context.window)
        wm.modal_handler_add(self)
        return {'RUNNING_MODAL'}

    def cancel(self, context):
        wm = context.window_manager
        wm.event_timer_remove(self._timer)

class StopMaintainingTiltOperator(Operator):
    bl_idname = "object.stop_maintaining_tilt"
    bl_label  = "Stop Maintaining Tilt"

    def execute(self, context):
        # This operator's purpose is to be a target for the UI,
        # the actual stopping logic is in the modal operator.
        return {'FINISHED'}

# ---------------------------
# Stroke Brush Properties
# ---------------------------
class StrokeBrushProperties(PropertyGroup):
    animation_mode: EnumProperty(
        name="Stroke Mode",
        items=[('ANIMATED', "Animated", ""), ('STATIC', "Static", "")],
        default='ANIMATED'
    )
    stroke_type: EnumProperty(
        name="Stroke Type",
        items=[('STATIC', "Static", ""), ('DYNAMIC', "Dynamic", "")],
        default='DYNAMIC'
    )
    normal_map_type: EnumProperty(
        name="Normal Map Type",
        items=[('STATIC', "Static", ""), ('DYNAMIC', "Dynamic", "")],
        default='DYNAMIC'
    )
    color_mixer: FloatProperty(
        name="Color Mixer",
        default=0.5,
        min=0.0,
        max=1.0,
        update=lambda s, c: update_color(c)
    )
    color: FloatVectorProperty(
        name="Base Color",
        subtype='COLOR',
        size=4,
        default=(1, 1, 1, 1),
        min=0.0,
        max=1.0,
        update=lambda s, c: update_color(c)
    )
    additional_base_colors: CollectionProperty(type=AdditionalColor)
    use_secondary_color: BoolProperty(
        name="Use Secondary",
        default=False,
        update=lambda s, c: update_color(c)
    )
    secondary_color: FloatVectorProperty(
        name="Secondary",
        subtype='COLOR',
        size=4,
        default=(1, 1, 1, 1),
        min=0.0,
        max=1.0,
        update=lambda s, c: update_color(c)
    )
    additional_secondary_colors: CollectionProperty(type=AdditionalColor)
    metallic: FloatProperty(
        name="Metallic",
        default=0.0,
        min=0.0,
        max=1.0,
        update=lambda s, c: update_material_properties(c)
    )
    roughness: FloatProperty(
        name="Roughness",
        default=0.5,
        min=0.0,
        max=1.0,
        update=lambda s, c: update_material_properties(c)
    )
    emission: FloatProperty(
        name="Emission",
        default=0.0,
        min=0.0,
        max=5.0,
        description="Controls emission strength",
        update=lambda s, c: update_material_properties(c)
    )
    subsurface_amount: FloatProperty(
        name="Subsurface",
        default=0.0,
        min=0.0,
        max=1.0,
        update=lambda s, c: update_material_properties(c)
    )
    use_alpha_channel: BoolProperty(
        name="Use Alpha Channel",
        default=True,
        description="Toggle connection of stroke image alpha to the BSDF Alpha",
        update=lambda s, c: update_alpha_channel(c)
    )

    # Tilt Properties
    global_tilt: FloatProperty(
        name="Global Tilt",
        default=0.0,
        min=-3.14159,
        max=3.14159,
        update=update_global_tilt # Direct function reference
    )
    maintain_tilt: BoolProperty(
        name="Maintain Tilt",
        default=False,
        update=lambda self, c: self.update_maintain_tilt(c)
    )
    mean_tilt: FloatProperty(
        name="Mean Tilt",
        default=0.0,
        min=-360.0,
        max=360.0
    )
    def update_maintain_tilt(self, context):
        if self.maintain_tilt:
            # FIX: Use 'INVOKE_DEFAULT' to properly start the modal operator
            bpy.ops.object.start_maintaining_tilt('INVOKE_DEFAULT')
        else:
            # The modal operator stops itself when it sees the property is false.
            pass

    selected_object: PointerProperty(
        name="Selected Object",
        type=bpy.types.Object
    )
    shrinkwrap_offset: FloatProperty(
        name="Shrinkwrap Offset",
        default=0.0,
        min=-10.0,
        max=10.0,
        update=lambda s, c: update_shrinkwrap_offset(c)
    )
    extrusion: FloatProperty(
        name="Extrusion",
        default=0.1,
        min=0.0,
        max=10.0,
        update=lambda s, c: update_extrusion(c)
    )
    extrusion_locked: FloatProperty(
        name="Extrusion (Locked)",
        default=0.1,
        min=0.0,
        max=1.0,
        update=lambda s, c: update_extrusion(c)
    )
    lock_depth_to_extrusion: BoolProperty(
        name="Lock Depth",
        default=False,
        update=lambda s, c: update_extrusion(c)
    )
    depth: FloatProperty(
        name="Depth",
        default=0.0,
        min=0.0,
        max=10.0,
        update=lambda s, c: update_extrusion(c)
    )
    use_solidify: BoolProperty(
        name="Solidify",
        description="Add a Solidify modifier to the active curve",
        default=False,
        update=update_solidify_modifier
    )
    solidify_thickness: FloatProperty(
        name="Thickness",
        description="Controls the thickness of the Solidify modifier",
        default=0.01,
        min=-10.0,
        max=10.0,
        update=update_solidify_modifier
    )
    solidify_offset: FloatProperty(
        name="Offset",
        description="Controls the offset of the Solidify modifier",
        default=-1.0,
        min=-1.0,
        max=1.0,
        update=update_solidify_modifier
    )
    displacement_height: FloatProperty(
        name="Height",
        default=0.0,
        min=0.0,
        max=10.0,
        update=lambda s, c: update_displacement(c)
    )
    displacement_midlevel: FloatProperty(
        name="Midlevel",
        default=0.0,
        min=0.0,
        max=1.0,
        update=lambda s, c: update_displacement(c)
    )
    displacement_scale: FloatProperty(
        name="Scale",
        default=0.0,
        min=0.0,
        max=10.0,
        update=lambda s, c: update_displacement(c)
    )
    add_subdivision: BoolProperty(
        name="Add Subdivision",
        default=False
    )
    optimized_viewport_strokes: BoolProperty(
        name="Optimize Viewport",
        default=False,
        update=lambda s, c: update_extras_strokes(c)
    )
    effect_type: EnumProperty(
        name="Effects",
        items=EFFECT_TYPES,
        default=EFFECT_NONE,
        update=effect_update_callback
    )
    # --- NEW: Wave Modifier Properties ---
    wave_height: FloatProperty(name="Height", default=0.2, min=0.0, max=10.0, update=update_wave_values)
    wave_width: FloatProperty(name="Width", default=0.44, min=0.0, max=10.0, update=update_wave_values)
    wave_narrowness: FloatProperty(name="Narrowness", default=10.0, min=0.1, max=20.0, update=update_wave_values)
    wave_speed: FloatProperty(name="Speed", default=0.03, min=0.0, max=1.0, update=update_wave_values)
    wave_motion_x: BoolProperty(name="Motion on X", default=False, update=update_wave_values)
    wave_motion_y: BoolProperty(name="Motion on Y", default=True, update=update_wave_values)

    effect_color_vec_mode: EnumProperty(
        name="Color/Alpha UV",
        items=[("OFF", "OFF", ""), ("COLOR", "Color", ""), ("FACPOS", "Fac/Distance", "")],
        default="COLOR",
        update=effect_update_callback
    )
    effect_normal_vec_mode: EnumProperty(
        name="Normal Map UV",
        items=[("OFF", "OFF", ""), ("COLOR", "Color", ""), ("FACPOS", "Fac/Distance", "")],
        default="COLOR",
        update=effect_update_callback
    )
    effect_magic_scale: FloatProperty(
        name="Magic Scale",
        default=5.0,
        min=0.0,
        max=100.0,
        update=effect_update_callback
    )
    effect_magic_distortion: FloatProperty(
        name="Magic Distortion",
        default=1.0,
        min=0.0,
        max=10.0,
        update=effect_update_callback
    )
    effect_magic_depth: IntProperty(
        name="Magic Depth",
        default=2,
        min=0,
        max=10,
        update=effect_update_callback
    )
    effect_voronoi_scale: FloatProperty(
        name="Voronoi Scale",
        default=5.0,
        min=0.0,
        max=100.0,
        update=effect_update_callback
    )
    effect_voronoi_smoothness: FloatProperty(
        name="Smoothness",
        default=0.0,
        min=0.0,
        max=1.0,
        update=effect_update_callback
    )
    effect_voronoi_exponent: FloatProperty(
        name="Exponent",
        default=2.5,
        min=0.0,
        max=10.0,
        update=effect_update_callback
    )
    effect_voronoi_randomness: FloatProperty(
        name="Randomness",
        default=1.0,
        min=0.0,
        max=1.0,
        update=effect_update_callback
    )
    effect_voronoi_feature: EnumProperty(
        name="Feature",
        items=[('F1', "F1", ""), ('F2', "F2", ""), ('SMOOTH_F1', "Smooth F1", ""), ('DISTANCE_TO_EDGE', "Distance to Edge", ""), ('N_SPHERE_RADIUS', "N Sphere Radius", "")],
        default='F1',
        update=effect_update_callback
    )
    effect_voronoi_distance: EnumProperty(
        name="Distance Metric",
        items=[('EUCLIDEAN', "Euclidean", ""), ('MANHATTAN', "Manhattan", ""), ('CHEBYCHEV', "Chebychev", ""), ('MINKOWSKI', "Minkowski", "")],
        default='EUCLIDEAN',
        update=effect_update_callback
    )
    effect_noise_scale: FloatProperty(
        name="Noise Scale",
        default=5.0,
        min=0.0,
        max=100.0,
        update=effect_update_callback
    )
    effect_noise_detail: FloatProperty(
        name="Detail",
        default=2.0,
        min=0.0,
        max=16.0,
        update=effect_update_callback
    )
    effect_noise_roughness: FloatProperty(
        name="Roughness",
        default=0.5,
        min=0.0,
        max=1.0,
        update=effect_update_callback
    )
    effect_noise_distortion: FloatProperty(
        name="Distortion",
        default=0.0,
        min=0.0,
        max=10.0,
        update=effect_update_callback
    )
    step_value: IntProperty(
        name="Step Value",
        description="Number of scene frames each stroke frame is held (step value)",
        default=1,
        min=1,
        max=12,
        update=lambda s, c: update_step_drivers(c)
    )
    normal_map_strength: FloatProperty(
        name="Normal Map Strength",
        description="Control the strength of the normal map for the stroke",
        default=0.4,
        min=0.0,
        max=1.0,
        update=lambda s, c: update_material_properties(c)
    )
    subsurface_radius: FloatVectorProperty(
        name="Subsurface Radius",
        subtype='XYZ',
        size=3,
        default=(1.0, 0.2, 0.1),
        min=0.0,
        max=10.0,
        description="Controls the radius for subsurface scattering (X, Y, Z)",
        update=lambda s, c: update_material_properties(c)
    )
    subsurface_scale: FloatProperty(
        name="Subsurface Scale",
        default=1.0,
        min=0.0,
        max=10.0,
        description="Controls the scale for subsurface scattering",
        update=lambda s, c: update_material_properties(c)
    )
    color_mixer_offset: FloatProperty(
        name="Color Mixer",
        description="Shift color stops left (-) or right (+)",
        default=0.0,
        min=-3.0,
        max=3.0,
        update=lambda s, c: update_color(c)
    )

# ---------------------------
# Addon Properties
# ---------------------------
class AddonProperties(PropertyGroup):
    active_mode: EnumProperty(
        name="Mode",
        items=[('STROKE_PEN', "Stroke Pen", ""), ('PAINTERLY_TEXTURE', "Painterly Texture", "")],
        default='STROKE_PEN'
    )
    update_checked: BoolProperty(default=False)
    update_available: BoolProperty(default=False)
    update_downloaded: BoolProperty(default=False)
    latest_version: StringProperty(default="")
    latest_changelog: StringProperty(default="")
    latest_url: StringProperty(default="")

class PainterlyProperties(PropertyGroup):
    stroke_length: IntProperty(name="Stroke Length", default=1200, min=60, max=6000)
    stroke_width: FloatProperty(name="Stroke Width", default=90.0, min=30.0, max=300.0)
    random_seed: IntProperty(name="Random Seed", default=42, min=1)
    randomness_intensity: FloatProperty(name="Stroke Randomness", default=0.7, min=0.0, max=1.0)
    stroke_opacity: FloatProperty(name="Stroke Opacity", default=1.0, min=0.1, max=1.0)
    randomize_stroke_length: BoolProperty(name="Randomize Stroke Length", default=False)
    stroke_length_min: IntProperty(name="Min Stroke Length", default=300, min=60, max=6000)
    image: PointerProperty(name="Image", type=bpy.types.Image)
    batch_mode: BoolProperty(default=False)
    batch_folder: StringProperty(name="Batch Output Folder", subtype='DIR_PATH', default="")
    batch_amount: IntProperty(
        name="Batch Mode Amount",
        default=10,
        min=1,
        max=100
    )
    override_with_custom_image: BoolProperty(name="Override with Custom Image", default=False)
    override_image_path: StringProperty(name="Custom Image Path", subtype='FILE_PATH', default="")

class RefreshPreviewsOperator(bpy.types.Operator):
    """Reload thumbnails for the current page in each browser"""
    bl_idname = "painterly.refresh_previews"
    bl_label  = "Refresh Previews"

    def execute(self, context):
        props = context.scene.painterly_folder_properties
        reinitialize_page_icons(props.stroke_folders,
                                props.current_stroke_index,
                                props.previews_per_page)
        reinitialize_page_icons(props.normal_map_folders,
                                props.current_normal_map_index,
                                props.previews_per_page)
        reinitialize_page_icons(props.preset_folders,
                                props.current_preset_index,
                                props.previews_per_page)
        self.report({'INFO'}, "Previews refreshed.")
        return {'FINISHED'}

@persistent
def painterly_load_post_handler(dummy):
    if painterly_frame_change_post not in bpy.app.handlers.frame_change_post:
        bpy.app.handlers.frame_change_post.append(painterly_frame_change_post)
        
    try:
        addon = bpy.context.preferences.addons.get(get_addon_key())
        if not addon:
            return
        prefs = addon.preferences
        scn = bpy.context.scene
        if not scn:
            return
        
        props = scn.painterly_folder_properties
        props.base_path = prefs.base_folder_path
        props.folder_configured = bool(prefs.base_folder_path)
        
        if props.folder_configured:
            scan_painterly_folders(bpy.context)
            
        print("[Painterly] root folder restored on file load")

        addon_props = bpy.context.scene.addon_properties
        addon_props.update_checked = False
        addon_props.update_available = False
        addon_props.update_downloaded = False
        addon_props.latest_version = ""
        addon_props.latest_changelog = ""
        addon_props.latest_url = ""
        if prefs.enable_auto_update:
            bpy.app.timers.register(lambda: bpy.ops.painterly.check_for_updates(), first_interval=1)

        # ——— MIGRATE any old‐version strokes so they aren’t “lost” ———
        for obj in bpy.context.scene.objects:
            if obj.type == 'CURVE':
                data = obj.data
                # old v2.x stored the stroke‐folder path on the Curve data itself
                if hasattr(data, "get") and "painterly_stroke_path" in data and "painterly_stroke_path" not in obj:
                    obj["painterly_stroke_path"] = data["painterly_stroke_path"]

    except Exception as exc:
        print("[Painterly] load_post handler failed:", exc)

class CheckForUpdatesOperator(Operator):
    bl_idname = "painterly.check_for_updates"
    bl_label = "Check for Updates"
    def execute(self, context):
        url = UPDATE_JSON_URL
        addon = context.preferences.addons.get(get_addon_key())
        if not addon:
            self.report({'ERROR'}, "Could not find addon preferences.")
            return {'CANCELLED'}
        prefs = addon.preferences
        
        if not prefs.enable_auto_update:
            self.report({'INFO'}, "Auto updates disabled.")
            return {'CANCELLED'}
        props = context.scene.addon_properties
        try:
            with urllib.request.urlopen(url) as response:
                data = response.read().decode('utf-8')
            info = json.loads(data)
            version_list = info.get("version", [])
            if not isinstance(version_list, list) or len(version_list) < 3:
                self.report({'ERROR'}, "Invalid version in JSON.")
                props.update_checked = True
                props.update_available = False
                props.update_downloaded = False
                return {'CANCELLED'}
            latest_version_tuple = tuple(version_list)
            latest_url = info.get("url", "")
            latest_changelog = info.get("changelog", "")
            if compare_versions(CURRENT_VERSION, latest_version_tuple) < 0:
                props.update_checked = True
                props.update_available = True
                props.update_downloaded = False
                props.latest_version = ".".join(map(str, latest_version_tuple))
                props.latest_changelog = latest_changelog
                props.latest_url = latest_url
                self.report({'INFO'}, f"New version {props.latest_version} available!")
            else:
                props.update_checked = True
                props.update_available = False
                props.update_downloaded = False
                props.latest_version = ""
                props.latest_changelog = ""
                props.latest_url = ""
                self.report({'INFO'}, "No updates available.")
        except Exception as e:
            self.report({'ERROR'}, f"Failed to check updates: {e}")
            props.update_checked = True
            props.update_available = False
            props.update_downloaded = False
        return {'FINISHED'}

class DownloadUpdateOperator(Operator):
    bl_idname = "painterly.download_update"
    bl_label = "Download Update"
    def execute(self, context):
        addon = context.preferences.addons.get(get_addon_key())
        if not addon:
            self.report({'ERROR'}, "Could not find addon preferences.")
            return {'CANCELLED'}
        prefs = addon.preferences
        if not prefs.enable_auto_update:
            self.report({'INFO'}, "Auto updates disabled.")
            return {'CANCELLED'}
        props = context.scene.addon_properties
        download_url = props.latest_url
        if not download_url:
            self.report({'ERROR'}, "No download URL found.")
            return {'CANCELLED'}
        try:
            with urllib.request.urlopen(download_url) as response:
                new_code = response.read()
            current_addon_dir = os.path.dirname(os.path.abspath(__file__))
            init_path = os.path.join(current_addon_dir, "__init__.py")
            backup_path = init_path + ".bak"
            if os.path.exists(backup_path):
                os.remove(backup_path)
            if os.path.exists(init_path):
                os.rename(init_path, backup_path)
            with open(init_path, "wb") as f:
                f.write(new_code)
            props.update_downloaded = True
            self.report({'INFO'}, "Update downloaded. Please restart Blender.")
        except Exception as e:
            self.report({'ERROR'}, f"Failed to download update: {e}")
            return {'CANCELLED'}
        return {'FINISHED'}

class RestartBlenderOperator(Operator):
    bl_idname = "painterly.restart_blender"
    bl_label = "Restart Blender"
    def execute(self, context):
        try:
            binary = bpy.app.binary_path
            blend_file = bpy.data.filepath
            args = [binary]
            if blend_file:
                args.append(blend_file)
            if os.name == 'nt':
                DETACHED_PROCESS = 0x00000008
                subprocess.Popen(args, creationflags=DETACHED_PROCESS)
            else:
                subprocess.Popen(args)
            bpy.ops.wm.quit_blender()
        except Exception as e:
            self.report({'WARNING'}, f"Failed to automatically restart Blender: {e}")
        return {'FINISHED'}

class RefreshFoldersOperator(Operator):
    bl_idname = "painterly.refresh_folders"
    bl_label = "Refresh Folders"
    def execute(self, context):
        addon = context.preferences.addons.get(get_addon_key())
        if not addon:
            self.report({'ERROR'}, "Could not find addon preferences.")
            return {'CANCELLED'}
        prefs = addon.preferences
        
        if prefs.base_folder_path and os.path.exists(prefs.base_folder_path):
            props = context.scene.painterly_folder_properties
            props.base_path = prefs.base_folder_path
            props.folder_configured = True
            scan_painterly_folders(context)
            self.report({'INFO'}, "Folders refreshed.")
        else:
            self.report({'ERROR'}, "Invalid base folder path")
        return {'FINISHED'}

class SetFolderOperator(Operator):
    bl_idname = "painterly.set_folder"
    bl_label = "Select Painterly Folder"
    filepath: StringProperty(subtype="DIR_PATH")
    def execute(self, context):
        addon = context.preferences.addons.get(get_addon_key())
        if not addon:
            self.report({'ERROR'}, "Could not find addon preferences.")
            return {'CANCELLED'}
        prefs = addon.preferences
        prefs.base_folder_path = self.filepath
        bpy.ops.wm.save_userpref()
        props = context.scene.painterly_folder_properties
        props.base_path = self.filepath
        props.folder_configured = True
        scan_painterly_folders(context)
        self.report({'INFO'}, "Base folder set.")
        return {'FINISHED'}
    def invoke(self, context, event):
        context.window_manager.fileselect_add(self)
        return {'RUNNING_MODAL'}

class NavigateFolderOperator(Operator):
    bl_idname = "painterly.navigate_folder"
    bl_label = "Navigate Folder"
    folder_type: StringProperty()
    direction: StringProperty()
    def navigate_collection(self, current_index, collection, grid_mode, previews_per_page):
        if len(collection) == 0:
            return 0
        if grid_mode:
            current_page = current_index // previews_per_page
            total_pages = (len(collection) - 1) // previews_per_page + 1
            if self.direction == 'NEXT':
                next_page = (current_page + 1) % total_pages
            else:
                next_page = (current_page - 1 + total_pages) % total_pages
            return next_page * previews_per_page
        else:
            if self.direction == 'NEXT':
                return (current_index + 1) % len(collection)
            else:
                return (current_index - 1 + len(collection)) % len(collection)
    def execute(self, context):
        props = context.scene.painterly_folder_properties
        if self.folder_type == 'stroke':
            props.current_stroke_index = self.navigate_collection(
                props.current_stroke_index, props.stroke_folders, props.show_stroke_grid, props.previews_per_page
            )
            reinitialize_page_icons(props.stroke_folders, props.current_stroke_index, props.previews_per_page)
        elif self.folder_type == 'normal':
            props.current_normal_map_index = self.navigate_collection(
                props.current_normal_map_index, props.normal_map_folders, props.show_normal_grid, props.previews_per_page
            )
            reinitialize_page_icons(props.normal_map_folders, props.current_normal_map_index, props.previews_per_page)
        elif self.folder_type == 'preset':
            props.current_preset_index = self.navigate_collection(
                props.current_preset_index, props.preset_folders, props.show_preset_grid, props.previews_per_page
            )
            reinitialize_page_icons(props.preset_folders, props.current_preset_index, props.previews_per_page)
        return {'FINISHED'}

class SelectPreviewOperator(Operator):
    bl_idname = "painterly.select_preview"
    bl_label = "Select Preview"
    folder_type: StringProperty()
    index: IntProperty()
    def execute(self, context):
        props = context.scene.painterly_folder_properties
        if self.folder_type == 'stroke':
            props.current_stroke_index = self.index
            props.show_stroke_grid = False
        elif self.folder_type == 'normal':
            props.current_normal_map_index = self.index
            props.show_normal_grid = False
        elif self.folder_type == 'preset':
            props.current_preset_index = self.index
            props.show_preset_grid = False
        return {'FINISHED'}

class SelectObjectOperator(Operator):
    bl_idname = "object.select_object"
    bl_label = "Select Object"
    def execute(self, context):
        context.scene.stroke_brush_properties.selected_object = context.object
        return {'FINISHED'}

class AutoStrokeOperator(Operator):
    bl_idname = "object.auto_stroke"
    bl_label = "Add Stroke"

    def execute(self, context):
        props = context.scene.stroke_brush_properties
        folders = context.scene.painterly_folder_properties
        
        addon_prefs = context.preferences.addons.get(get_addon_key()).preferences

        if len(folders.stroke_folders) == 0:
            self.report({'ERROR'}, "No stroke folders available.")
            return {'CANCELLED'}
        if len(folders.normal_map_folders) == 0:
            self.report({'ERROR'}, "No normal map folders available.")
            return {'CANCELLED'}
        try:
            stroke_folder = folders.stroke_folders[folders.current_stroke_index]
            normal_folder = folders.normal_map_folders[folders.current_normal_map_index]

            stroke_name = stroke_folder.name.replace(" ", "_")
            base_obj_name = f"Painterly_{stroke_name}"
            
            # --- FIX INTEGRATED HERE ---
            # Proper deferred curve creation (then kill the default segment)
            bpy.ops.curve.primitive_bezier_curve_add(enter_editmode=False, align='WORLD', location=(0,0,0))
            new_curve = context.active_object
            new_curve.name = base_obj_name
            curve_data = new_curve.data
            curve_data.name = base_obj_name + "_Curve"
            # remove the initial prefab spline so nothing shows until you draw
            # (this empties the curve, your modal draw will add new splines)
            while curve_data.splines:
                curve_data.splines.remove(curve_data.splines[0])
            # --- END OF FIX INTEGRATION ---
            
            new_curve['painterly_stroke_path'] = stroke_folder.path

            if props.lock_depth_to_extrusion:
                new_curve.data.extrude = props.extrusion_locked
            else:
                new_curve.data.extrude = props.extrusion
            if props.optimized_viewport_strokes:
                new_curve.data.resolution_u = 3
                new_curve.data.render_resolution_u = 12
            if props.add_subdivision:
                mod = new_curve.modifiers.new(name="Painterly Subdivision", type='SUBSURF')
                mod.levels = 2
                mod.render_levels = 2
            mat = bpy.data.materials.new(f"{new_curve.name}_Material")
            mat.use_nodes = True
            nt = mat.node_tree
            nodes = nt.nodes
            links = nt.links
            for n in list(nodes):
                nodes.remove(n)
            mat_out = nodes.new("ShaderNodeOutputMaterial")
            mat_out.location = (600, 300)
            if props.animation_mode != 'STATIC':
                base_color_frame = nodes.new("NodeFrame")
                base_color_frame.label = "Base Color Nodes"
                base_color_frame.location = (-1300, 400)
                normal_map_frame = nodes.new("NodeFrame")
                normal_map_frame.label = "Normal Map Nodes"
                normal_map_frame.location = (-1300, 100)
                mix_shader_frame = nodes.new("NodeFrame")
                mix_shader_frame.label = "Mix Shader Chain"
                mix_shader_frame.location = (-400, 400)
                displacement_frame = nodes.new("NodeFrame")
                displacement_frame.label = "Displacement"
                displacement_frame.location = (-100, -300)
                stroke_files = sorted(
                    [f for f in os.listdir(stroke_folder.path) if f.lower().endswith('.png')],
                    key=natural_keys
                )
                normal_files = sorted(
                    [f for f in os.listdir(normal_folder.path) if f.lower().endswith('.png')],
                    key=natural_keys
                )
                if not stroke_files:
                    self.report({'ERROR'}, "No .png stroke files in: " + stroke_folder.path)
                    bpy.data.objects.remove(new_curve)
                    bpy.data.curves.remove(curve_data)
                    return {'CANCELLED'}
                if not normal_files:
                    self.report({'ERROR'}, "No .png normal map files found in: " + normal_folder.path)
                    bpy.data.objects.remove(new_curve)
                    bpy.data.curves.remove(curve_data)
                    return {'CANCELLED'}
                frame_count = len(stroke_files)
                mat["frame_count"] = frame_count
                normal_count = len(normal_files)
                transp = nodes.new("ShaderNodeBsdfTransparent")
                transp.location = (-600, 300)
                base_nodes = []
                normal_nodes = []
                for i in range(frame_count):
                    img_node = nodes.new("ShaderNodeTexImage")
                    img_node.parent = base_color_frame
                    img_node.name = f"StrokeFrame_{i+1}"
                    img_path = os.path.join(stroke_folder.path, stroke_files[i])
                    img_node.image = bpy.data.images.load(img_path)
                    img_node.location = (-1200, 400 - i * 300)
                    ramp_node = nodes.new("ShaderNodeValToRGB")
                    ramp_node.parent = base_color_frame
                    ramp_node.name = f"StrokeColorRamp_{i+1}"
                    ramp_node.location = (-900, 400 - i * 300)
                    links.new(img_node.outputs["Color"], ramp_node.inputs["Fac"])
                    update_ramp_node(ramp_node)
                    bsdf_node = nodes.new("ShaderNodeBsdfPrincipled")
                    bsdf_node.parent = base_color_frame
                    bsdf_node.name = f"StrokeBSDF_{i+1}"
                    bsdf_node.location = (-600, 400 - i * 300)
                    links.new(ramp_node.outputs["Color"], bsdf_node.inputs["Base Color"])
                    if "Emission" in bsdf_node.inputs:
                        links.new(ramp_node.outputs["Color"], bsdf_node.inputs["Emission"])
                    if props.use_alpha_channel:
                        links.new(img_node.outputs["Alpha"], bsdf_node.inputs["Alpha"])
                    bsdf_node.inputs["Metallic"].default_value = props.metallic
                    bsdf_node.inputs["Roughness"].default_value = props.roughness
                    if "Subsurface" in bsdf_node.inputs:
                        bsdf_node.inputs["Subsurface"].default_value = props.subsurface_amount
                    if "Subsurface Radius" in bsdf_node.inputs:
                        bsdf_node.inputs["Subsurface Radius"].default_value = props.subsurface_radius
                    if "Subsurface Scale" in bsdf_node.inputs:
                        bsdf_node.inputs["Subsurface Scale"].default_value = props.subsurface_scale
                    bsdf_node.inputs["Emission Strength"].default_value = props.emission
                    base_nodes.append(bsdf_node)
                    normal_img_node = nodes.new("ShaderNodeTexImage")
                    normal_img_node.parent = normal_map_frame
                    normal_img_node.name = f"NormalFrame_{i+1}"
                    normal_img_path = os.path.join(normal_folder.path, normal_files[i % normal_count])
                    normal_img_node.image = bpy.data.images.load(normal_img_path)
                    normal_img_node.image.colorspace_settings.name = 'Non-Color'
                    normal_img_node.location = (-1200, 100 - i * 300)
                    normal_map_node = nodes.new("ShaderNodeNormalMap")
                    normal_map_node.parent = normal_map_frame
                    normal_map_node.name = f"Normal Map_{i+1}"
                    normal_map_node.location = (-900, 100 - i * 300)
                    links.new(normal_img_node.outputs["Color"], normal_map_node.inputs["Color"])
                    normal_map_node.space = 'OBJECT'
                    normal_map_node.inputs['Strength'].default_value = props.normal_map_strength
                    links.new(normal_map_node.outputs["Normal"], base_nodes[i].inputs["Normal"])
                    normal_nodes.append(normal_map_node)
                mix_nodes = []
                mix_prev = nodes.new("ShaderNodeMixShader")
                mix_prev.parent = mix_shader_frame
                mix_prev.name = "Mix Shader_1" # Underscore to help parsing
                mix_prev.location = (-400, 400)
                links.new(transp.outputs["BSDF"], mix_prev.inputs[1])
                links.new(base_nodes[0].outputs["BSDF"], mix_prev.inputs[2])
                drv = mix_prev.inputs[0].driver_add("default_value").driver
                
                # --- ROBUST DRIVER EXPRESSION ---
                drv.expression = "int(((frame - 1) / step)) % max(fc, 1) + 1 == 1"
                
                driver = drv
                vars = {v.name: v for v in driver.variables}
                if "frame" not in vars:
                    vars["frame"] = driver.variables.new()
                    vars["frame"].name = "frame"
                if "step" not in vars:
                    vars["step"] = driver.variables.new()
                    vars["step"].name = "step"
                if "fc" not in vars:
                    vars["fc"] = driver.variables.new()
                    vars["fc"].name = "fc"
                
                vars["frame"].targets[0].id_type = 'SCENE'
                vars["frame"].targets[0].id = context.scene
                vars["frame"].targets[0].data_path = "frame_current"

                vars["step"].targets[0].id_type = 'SCENE'
                vars["step"].targets[0].id = context.scene
                vars["step"].targets[0].data_path = "stroke_brush_properties.step_value"
                
                vars["fc"].targets[0].id_type = 'MATERIAL'
                vars["fc"].targets[0].id = mat
                vars["fc"].targets[0].data_path = '["frame_count"]'
                mix_nodes.append(mix_prev)

                for i in range(1, frame_count):
                    mix_node = nodes.new("ShaderNodeMixShader")
                    mix_node.parent = mix_shader_frame
                    mix_node.name = f"Mix Shader_{i+1}" # Underscore to help parsing
                    mix_node.location = (-400, 400 - i * 200)
                    links.new(mix_nodes[-1].outputs["Shader"], mix_node.inputs[1])
                    links.new(base_nodes[i].outputs["BSDF"], mix_node.inputs[2])
                    drv = mix_node.inputs[0].driver_add("default_value").driver

                    # --- ROBUST DRIVER EXPRESSION ---
                    drv.expression = f"int(((frame - 1) / step)) % max(fc, 1) + 1 == {i+1}"
                    
                    driver = drv
                    vars = {v.name: v for v in driver.variables}
                    if "frame" not in vars:
                        vars["frame"] = driver.variables.new()
                        vars["frame"].name = "frame"
                    if "step" not in vars:
                        vars["step"] = driver.variables.new()
                        vars["step"].name = "step"
                    if "fc" not in vars:
                        vars["fc"] = driver.variables.new()
                        vars["fc"].name = "fc"
                    
                    vars["frame"].targets[0].id_type = 'SCENE'
                    vars["frame"].targets[0].id = context.scene
                    vars["frame"].targets[0].data_path = "frame_current"

                    vars["step"].targets[0].id_type = 'SCENE'
                    vars["step"].targets[0].id = context.scene
                    vars["step"].targets[0].data_path = "stroke_brush_properties.step_value"
                    
                    vars["fc"].targets[0].id_type = 'MATERIAL'
                    vars["fc"].targets[0].id = mat
                    vars["fc"].targets[0].data_path = '["frame_count"]'
                    mix_nodes.append(mix_node)
                links.new(mix_nodes[-1].outputs["Shader"], mat_out.inputs["Surface"])
                disp_node = nodes.new("ShaderNodeDisplacement")
                disp_node.parent = displacement_frame
                disp_node.name = "Displacement"
                disp_node.location = (-100, -300)
                disp_node.inputs["Height"].default_value = props.displacement_height
                disp_node.inputs["Midlevel"].default_value = props.displacement_midlevel
                disp_node.inputs["Scale"].default_value = props.displacement_scale
                links.new(normal_nodes[0].outputs["Normal"], disp_node.inputs["Normal"])
                links.new(disp_node.outputs["Displacement"], mat_out.inputs["Displacement"])
            else:
                base_color_frame = nodes.new("NodeFrame")
                base_color_frame.label = "Base Color Nodes"
                base_color_frame.location = (-1300, 300)
                normal_map_frame = nodes.new("NodeFrame")
                normal_map_frame.label = "Normal Map Nodes"
                normal_map_frame.location = (-1300, 0)
                displacement_frame = nodes.new("NodeFrame")
                displacement_frame.label = "Displacement"
                displacement_frame.location = (-100, -300)
                stroke_files = sorted(
                    [f for f in os.listdir(stroke_folder.path) if f.lower().endswith('.png')],
                    key=natural_keys
                )
                normal_files = sorted(
                    [f for f in os.listdir(normal_folder.path) if f.lower().endswith('.png')],
                    key=natural_keys
                )
                if not stroke_files:
                    self.report({'ERROR'}, "No .png stroke files in: " + stroke_folder.path)
                    bpy.data.objects.remove(new_curve)
                    bpy.data.curves.remove(curve_data)
                    return {'CANCELLED'}
                if not normal_files:
                    self.report({'ERROR'}, "No .png normal map files found in: " + normal_folder.path)
                    bpy.data.objects.remove(new_curve)
                    bpy.data.curves.remove(curve_data)
                    return {'CANCELLED'}
                img_node = nodes.new("ShaderNodeTexImage")
                img_node.parent = base_color_frame
                img_node.name = "StrokeFrame_1"
                img_path = os.path.join(stroke_folder.path, stroke_files[0])
                img_node.image = bpy.data.images.load(img_path)
                img_node.location = (-1200, 300)
                ramp_node = nodes.new("ShaderNodeValToRGB")
                ramp_node.parent = base_color_frame
                ramp_node.name = "StrokeColorRamp_1"
                ramp_node.location = (-900, 300)
                links.new(img_node.outputs["Color"], ramp_node.inputs["Fac"])
                update_ramp_node(ramp_node)
                bsdf_node = nodes.new("ShaderNodeBsdfPrincipled")
                bsdf_node.parent = base_color_frame
                bsdf_node.name = "StrokeBSDF_1"
                bsdf_node.location = (-600, 300)
                links.new(ramp_node.outputs["Color"], bsdf_node.inputs["Base Color"])
                if "Emission" in bsdf_node.inputs:
                    links.new(ramp_node.outputs["Color"], bsdf_node.inputs["Emission"])
                if props.use_alpha_channel:
                    links.new(img_node.outputs["Alpha"], bsdf_node.inputs["Alpha"])
                bsdf_node.inputs["Metallic"].default_value = props.metallic
                bsdf_node.inputs["Roughness"].default_value = props.roughness
                if "Subsurface" in bsdf_node.inputs:
                    bsdf_node.inputs["Subsurface"].default_value = props.subsurface_amount
                if "Subsurface Radius" in bsdf_node.inputs:
                    bsdf_node.inputs["Subsurface Radius"].default_value = props.subsurface_radius
                if "Subsurface Scale" in bsdf_node.inputs:
                    bsdf_node.inputs["Subsurface Scale"].default_value = props.subsurface_scale
                if "Emission" in bsdf_node.inputs:
                    bsdf_node.inputs["Emission Strength"].default_value = props.emission
                normal_img_node = nodes.new("ShaderNodeTexImage")
                normal_img_node.parent = normal_map_frame
                normal_img_node.name = "NormalFrame_1"
                normal_img_path = os.path.join(normal_folder.path, normal_files[0])
                normal_img_node.image = bpy.data.images.load(normal_img_path)
                normal_img_node.image.colorspace_settings.name = 'Non-Color'
                normal_img_node.location = (-1200, 0)
                normal_map_node = nodes.new("ShaderNodeNormalMap")
                normal_map_node.parent = normal_map_frame
                normal_map_node.name = "Normal Map_1" # Underscore to help parsing
                normal_map_node.location = (-900, 0)
                links.new(normal_img_node.outputs["Color"], normal_map_node.inputs["Color"])
                normal_map_node.space = 'OBJECT'
                normal_map_node.inputs['Strength'].default_value = props.normal_map_strength
                links.new(normal_map_node.outputs["Normal"], bsdf_node.inputs["Normal"])
                disp_node = nodes.new("ShaderNodeDisplacement")
                disp_node.parent = displacement_frame
                disp_node.name = "Displacement"
                disp_node.location = (-100, -300)
                disp_node.inputs["Height"].default_value = 0
                disp_node.inputs["Midlevel"].default_value = 0
                disp_node.inputs["Scale"].default_value = 0
                links.new(normal_map_node.outputs["Normal"], disp_node.inputs["Normal"])
                links.new(disp_node.outputs["Displacement"], mat_out.inputs["Displacement"])
                links.new(bsdf_node.outputs["BSDF"], mat_out.inputs["Surface"])
            new_curve.data.materials.append(mat)
            update_material_properties(context)
            update_extrusion(context)
            update_extras_strokes(context)
            update_solidify_modifier(props, context)
            bpy.ops.object.mode_set(mode='EDIT')
            update_effect_nodes(context)
            self.report({'INFO'}, "Stroke added successfully.")
            return {'FINISHED'}
        except Exception as e:
            if 'new_curve' in locals() and new_curve and new_curve.name in bpy.data.objects:
                bpy.data.objects.remove(new_curve, do_unlink=True)
            if 'curve_data' in locals() and curve_data and curve_data.name in bpy.data.curves:
                bpy.data.curves.remove(curve_data)
            if 'mat' in locals() and mat and mat.name in bpy.data.materials:
                 if mat.users == 0:
                    bpy.data.materials.remove(mat)

            self.report({'ERROR'}, f"Failed to create stroke: {e}")
            import traceback
            traceback.print_exc()
            return {'CANCELLED'}

class AutoBakeOperator(Operator):
    bl_idname = "texture.auto_bake"
    bl_label = "Auto Bake"
    def execute(self, context):
        scene = context.scene
        stylized_props = scene.stylized_painterly_properties
        obj = context.active_object
        if not obj or obj.type != 'MESH':
            self.report({'ERROR'}, "Active object is not a mesh")
            return {'CANCELLED'}
        try:
            bpy.context.scene.render.engine = 'CYCLES'
            bpy.ops.object.mode_set(mode='OBJECT')
            mat = obj.active_material or bpy.data.materials.new(name="PainterlyMaterial")
            obj.active_material = mat
            mat.use_nodes = True
            nds = mat.node_tree.nodes
            lnks = mat.node_tree.links
            bsdf = nds.get("Principled BSDF") or nds.new("ShaderNodeBsdfPrincipled")
            tex_image = nds.new('ShaderNodeTexImage')
            image_name = f"{obj.name}_NORM_MAP"
            if image_name in bpy.data.images:
                image = bpy.data.images[image_name]
            else:
                image = bpy.data.images.new(name=image_name, width=1024, height=1024)
            tex_image.image = image
            lnks.new(bsdf.inputs['Base Color'], tex_image.outputs['Color'])
            normal_map_node = nds.new('ShaderNodeNormalMap')
            normal_map_node.space = 'OBJECT'
            normal_map_node.inputs['Strength'].default_value = 0.4
            lnks.new(normal_map_node.inputs['Color'], tex_image.outputs['Color'])
            lnks.new(bsdf.inputs['Normal'], normal_map_node.outputs['Normal'])
            scn = bpy.context.scene
            scn.render.bake.use_selected_to_active = False
            scn.render.bake.margin = 3
            scn.render.bake.use_clear = True
            scn.cycles.bake_type = 'NORMAL'
            scn.render.bake.normal_space = 'OBJECT'
            mat.node_tree.nodes.active = tex_image
            bpy.ops.object.bake(type='NORMAL')
            self.report({'INFO'}, "Baking completed successfully")
            stylized_props.image = image
            image.pack()
            return {'FINISHED'}
        except Exception as e:
            self.report({'ERROR'}, f"Baking failed: {e}")
            return {'CANCELLED'}

class PainterlyEffectOperator(Operator):
    bl_idname = "texture.apply_painterly_effect"
    bl_label = "Apply Painterly Effect"
    bl_options = {'REGISTER', 'UNDO'}
    def execute(self, context):
        if not check_pillow():
            self.report({'ERROR'}, "PIL not installed. Please click the 'Install Dependencies (PIL)' button below.")
            return {'CANCELLED'}
        scene = context.scene
        stylized_props = scene.stylized_painterly_properties
        folder_props = scene.painterly_folder_properties
        obj = context.active_object
        if obj.active_material is None or stylized_props.image is None:
            bpy.ops.texture.auto_bake()
        if not stylized_props.image:
            self.report({'ERROR'}, "Auto Bake failed; cannot apply Painterly Effect.")
            return {'CANCELLED'}
        final_image = stylized_props.image
        if len(folder_props.preset_folders) == 0:
            self.report({'ERROR'}, "No preset folders available.")
            return {'CANCELLED'}
        current_preset = folder_props.preset_folders[folder_props.current_preset_index]
        brush_stroke_path = current_preset.path
        brush_stroke_images = [os.path.join(brush_stroke_path, f)
                               for f in os.listdir(brush_stroke_path)
                               if f.lower().endswith('.png')]
        if not brush_stroke_images:
            self.report({'ERROR'}, "No brush stroke images found in the selected preset.")
            return {'CANCELLED'}
        if stylized_props.batch_mode:
            if not stylized_props.batch_folder or not os.path.exists(stylized_props.batch_folder):
                self.report({'ERROR'}, "Please select a valid batch folder.")
                return {'CANCELLED'}
            for i in range(stylized_props.batch_amount):
                seed = stylized_props.random_seed
                success, out_image = self.run_painterly_once(
                    context.active_object, stylized_props, brush_stroke_images,
                    override_path=None, random_seed=seed
                )
                if not success:
                    return {'CANCELLED'}
                obj = context.active_object
                out_name = f"{obj.name}_PAINTERLY_{i+1}.png"
                out_path = os.path.join(stylized_props.batch_folder, out_name)
                out_image.filepath_raw = out_path
                out_image.file_format = 'PNG'
                out_image.save()
            self.report({'INFO'}, f"Batch completed. {stylized_props.batch_amount} images saved.")
            return {'FINISHED'}
        else:
            seed = stylized_props.random_seed
            success, out_image = self.run_painterly_once(
                context.active_object, stylized_props, brush_stroke_images,
                override_path=None, random_seed=seed
            )
            if not success:
                return {'CANCELLED'}
            self.report({'INFO'}, "Painterly effect applied successfully.")
            return {'FINISHED'}
    def run_painterly_once(self, obj, stylized_props, brush_stroke_images, override_path=None, random_seed=42):
        try:
            from PIL import Image, ImageFilter
        except ImportError:
            self.report({'ERROR'}, "PIL not installed or not found.")
            return False, None
        if override_path:
            try:
                external_pil = Image.open(override_path).convert("RGBA")
                w, h = external_pil.size
                data = np.array(external_pil).astype(np.float32) / 255.0
                data_flat = data.flatten()
                override_img_name = "OVERRIDE_IMAGE"
                if override_img_name in bpy.data.images:
                    old_img = bpy.data.images[override_img_name]
                    bpy.data.images.remove(old_img)
                blender_override_img = bpy.data.images.new(override_img_name, width=w, height=h)
                blender_override_img.pixels = data_flat
                final_image = blender_override_img
            except Exception as e:
                self.report({'ERROR'}, f"Failed to load override image: {e}")
                return False, None
        else:
            final_image = stylized_props.image
            if not final_image:
                return False, None
        success, out_image = self.apply_painterly_effect_generic(
            obj, final_image, brush_stroke_images,
            stylized_props.stroke_length, stylized_props.stroke_width,
            random_seed, stylized_props.randomness_intensity, True,
            stylized_props.stroke_opacity,
            stylized_props.randomize_stroke_length,
            stylized_props.stroke_length_min
        )
        return success, out_image
    def apply_painterly_effect_generic(self, obj, image, brush_stroke_images,
                                       stroke_length, stroke_width, random_seed,
                                       randomness_intensity, color_variation,
                                       stroke_opacity, randomize_stroke_length,
                                       stroke_length_min):
        try:
            from PIL import Image, ImageFilter
        except ImportError:
            self.report({'ERROR'}, "PIL not installed.")
            return False, None
        import random
        random.seed(random_seed)
        w, h = image.size
        data = np.array(image.pixels[:]).reshape(h, w, 4) * 255
        base_pil = Image.fromarray(data.astype(np.uint8), 'RGBA')
        painterly_img = Image.new("RGBA", (w, h), (255, 255, 255, 0))
        if base_pil.mode == "RGBA":
            gray_base = base_pil.convert("L")
            edges = gray_base.filter(ImageFilter.FIND_EDGES)
            edge_map = np.array(edges)
        else:
            edge_map = None
        loaded_brushes = []
        for p in brush_stroke_images:
            try:
                b_img = Image.open(p).convert("RGBA")
                loaded_brushes.append(b_img)
            except:
                continue
        if not loaded_brushes:
            self.report({'ERROR'}, "No valid brush strokes found.")
            return False, None
        factor = 500.0 / 9.0
        overbleed = 10
        num_strokes = int(randomness_intensity * w * h / factor)
        small_base = 0.05 * stroke_length
        big_base = small_base * 5.0
        stroke_width_scaled = stroke_width * 0.5
        skip_non_edge_prob = 0.3
        skip_edge_prob = 0.2
        EDGE_THRESHOLD = 40
        tasks = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=None) as executor:
            for _ in range(num_strokes):
                x = random.randint(overbleed, w - overbleed)
                y = random.randint(overbleed, h - overbleed)
                px = base_pil.getpixel((x, y))
                if px[0] < 10 and px[1] < 10 and px[2] < 10:
                    continue
                if px[3] == 0:
                    continue
                angle = random.uniform(0, 360)
                chosen_length = float(stroke_length)
                if randomize_stroke_length:
                    chosen_length = random.uniform(stroke_length_min, stroke_length)
                if edge_map is not None:
                    ed_val = edge_map[y, x]
                    if ed_val > EDGE_THRESHOLD:
                        length_val = random.uniform(0.8, 1.2) * small_base
                        if random.random() < skip_edge_prob:
                            continue
                    else:
                        length_val = random.uniform(0.8, 1.2) * big_base
                        if random.random() < skip_non_edge_prob:
                            continue
                    chosen_length = length_val
                chosen_brush = random.choice(loaded_brushes)
                tasks.append(executor.submit(
                    self.apply_stroke_simple,
                    painterly_img, chosen_brush,
                    x, y, angle, chosen_length,
                    stroke_width_scaled, stroke_opacity,
                    color_variation, px
                ))
            concurrent.futures.wait(tasks)
        combined = np.array(painterly_img).flatten() / 255.0
        paint_name = f"{obj.active_material.name}_PAINTERLY"
        if paint_name in bpy.data.images:
            old = bpy.data.images[paint_name]
            bpy.data.images.remove(old)
        blender_res = bpy.data.images.new(paint_name, width=w, height=h)
        blender_res.pixels = combined
        blender_res.pack()
        mat = obj.active_material or bpy.data.materials.new(name="PainterlyMaterial")
        obj.active_material = mat
        mat.use_nodes = True
        nds = mat.node_tree.nodes
        lnks = mat.node_tree.links
        bsdf = nds.get("Principled BSDF") or nds.new("ShaderNodeBsdfPrincipled")
        tex_img = nds.new('ShaderNodeTexImage')
        tex_img.image = blender_res
        tex_img.image.colorspace_settings.name = 'Non-Color'
        lnks.new(bsdf.inputs['Base Color'], tex_img.outputs['Color'])
        lnks.new(bsdf.inputs['Alpha'], tex_img.outputs['Alpha'])
        normal_map_node = nds.new('ShaderNodeNormalMap')
        normal_map_node.space = 'OBJECT'
        normal_map_node.inputs['Strength'].default_value = 0.4
        lnks.new(normal_map_node.inputs['Color'], tex_img.outputs['Color'])
        lnks.new(bsdf.inputs['Normal'], normal_map_node.outputs['Normal'])
        return True, blender_res

    def apply_stroke_simple(self, painterly_image, brush_stroke,
                            x, y, angle, length,
                            stroke_width, stroke_opacity,
                            color_variation, base_color):
        from PIL import Image
        try:
            import random
            brush_resized = brush_stroke.resize((int(stroke_width), int(stroke_width)), Image.LANCZOS)
            brush_rotated = brush_resized.rotate(angle, expand=True)
            if color_variation:
                c_r = base_color[0] + random.randint(-30, 30)
                c_g = base_color[1] + random.randint(-30, 30)
                c_b = base_color[2] + random.randint(-30, 30)
                color = ( int(max(0, min(255, c_r))),
                          int(max(0, min(255, c_g))),
                          int(max(0, min(255, c_b))),
                          int(stroke_opacity * 255) )
            else:
                color = (base_color[0], base_color[1], base_color[2], int(stroke_opacity * 255))
            mask = brush_rotated.split()[3]
            colored = Image.new("RGBA", brush_rotated.size)
            for i in range(colored.size[0]):
                for j in range(colored.size[1]):
                    p = brush_rotated.getpixel((i, j))
                    if p[3] > 0:
                        colored.putpixel((i, j), color)
            off_x = int(x - colored.size[0] * 0.5)
            off_y = int(y - colored.size[1] * 0.5)
            base_crop = painterly_image.crop((off_x, off_y, off_x + colored.size[0], off_y + colored.size[1]))
            base_crop = Image.alpha_composite(base_crop, colored)
            painterly_image.paste(base_crop, (off_x, off_y), mask)
        except Exception as ex:
            print("Error applying stroke in thread:", ex)

class AddDisplacementOperator(Operator):
    bl_idname = "texture.add_displacement"
    bl_label = "Add Displacement"
    def execute(self, context):
        obj = context.active_object
        if not obj or obj.type != 'MESH':
            self.report({'ERROR'}, "Active object is not a mesh")
            return {'CANCELLED'}
        try:
            mat = obj.active_material
            if not mat:
                mat = bpy.data.materials.new(name="PainterlyMaterial")
                obj.active_material = mat
            mat.use_nodes = True
            nds = mat.node_tree.nodes
            lnks = mat.node_tree.links
            bsdf = nds.get("Principled BSDF") or nds.new("ShaderNodeBsdfPrincipled")
            normal_map_node = nds.get("Normal Map") or nds.new("ShaderNodeNormalMap")
            disp_node = nds.new("ShaderNodeDisplacement")
            disp_node.name = "Displacement"
            disp_node.location = (0, -300)
            mat_out = nds.get("Material Output")
            if not mat_out:
                mat_out = nds.new("ShaderNodeOutputMaterial")
            lnks.new(disp_node.outputs["Displacement"], mat_out.inputs["Displacement"])
            disp_node.inputs["Height"].default_value = context.scene.stroke_brush_properties.displacement_height
            disp_node.inputs["Midlevel"].default_value = context.scene.stroke_brush_properties.displacement_midlevel
            disp_node.inputs["Scale"].default_value = context.scene.stroke_brush_properties.displacement_scale
            if context.scene.stroke_brush_properties.animation_mode != 'STATIC':
                normal_nodes = [n for n in nds if n.name.startswith("Normal Map")]
                if normal_nodes:
                    normal_nodes.sort(key=lambda n: int(n.name.split("_")[-1]) if n.name.split("_")[-1].isdigit() else 0)
                    chain_output = normal_nodes[0].outputs["Normal"]
                    mat["frame_count"] = len(normal_nodes)
                    for i in range(1, len(normal_nodes)):
                        mix_rgb = nds.new("ShaderNodeMixRGB")
                        mix_rgb.name = f"DispMix_{i+1}"
                        mix_rgb.location = (-300, -300 - i * 150)
                        mix_rgb.blend_type = 'MIX'
                        lnks.new(normal_nodes[i].outputs["Normal"], mix_rgb.inputs[1])
                        lnks.new(chain_output, mix_rgb.inputs[2])
                        drv = mix_rgb.inputs["Fac"].driver_add("default_value").driver
                        # --- ROBUST DRIVER EXPRESSION ---
                        drv.expression = f"1 - (int(((frame - 1) / step)) % max(fc, 1) + 1 == {i+1})"
                        
                        driver = drv
                        vars = {v.name: v for v in driver.variables}
                        if "frame" not in vars:
                            vars["frame"] = driver.variables.new()
                            vars["frame"].name = "frame"
                        if "step" not in vars:
                            vars["step"] = driver.variables.new()
                            vars["step"].name = "step"
                        if "fc" not in vars:
                            vars["fc"] = driver.variables.new()
                            vars["fc"].name = "fc"
                        
                        vars["frame"].targets[0].id_type = 'SCENE'
                        vars["frame"].targets[0].id = context.scene
                        vars["frame"].targets[0].data_path = "frame_current"

                        vars["step"].targets[0].id_type = 'SCENE'
                        vars["step"].targets[0].id = context.scene
                        vars["step"].targets[0].data_path = "stroke_brush_properties.step_value"
                        
                        vars["fc"].targets[0].id_type = 'MATERIAL'
                        vars["fc"].targets[0].id = mat
                        vars["fc"].targets[0].data_path = '["frame_count"]'

                        chain_output = mix_rgb.outputs["Color"]
                    lnks.new(chain_output, disp_node.inputs["Normal"])
                    lnks.new(disp_node.outputs["Displacement"], mat_out.inputs["Displacement"])
            self.report({'INFO'}, "Displacement added.")
            return {'FINISHED'}
        except Exception as e:
            self.report({'ERROR'}, f"Error adding displacement: {e}")
            return {'CANCELLED'}

# ---------------------------
# UI Panel Helper Functions
# ---------------------------

def get_stroke_preset_item(obj, folder_props):
    if not obj:
        return None
    # support old curves which put the path on obj.data instead of obj
    path = obj.get("painterly_stroke_path") or getattr(obj.data, "get", lambda k: None)("painterly_stroke_path")
    if not path:
        return None
        
    for item in folder_props.stroke_folders:
        if os.path.normpath(path).startswith(os.path.normpath(item.path)):
             return item
    return None
    
def get_stroke_colors(obj):
    colors = []
    if not obj or not obj.active_material or not obj.active_material.node_tree:
        return colors
        
    mat_nodes = obj.active_material.node_tree.nodes
    ramp_node = mat_nodes.get("StrokeColorRamp_1") # Check static/first frame
    
    if ramp_node:
        elements = ramp_node.color_ramp.elements
        for i in range(min(len(elements), 3)):
             colors.append(elements[i].color)
             
    return colors

class StrokeBrushPanel(Panel):
    bl_label = "Painterly Add-on"
    bl_idname = "PAINTERLY_PT_PainterlyPanel"
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = "Painterly"
    def draw(self, context):
        layout = self.layout
        addon_key = get_addon_key()
        
        addon_prefs_owner = context.preferences.addons.get(addon_key)
        if not addon_prefs_owner:
            layout.label(text="Could not load Painterly preferences.")
            return
        prefs = addon_prefs_owner.preferences
        
        scene = context.scene
        addon_props = scene.addon_properties
        folder_props = scene.painterly_folder_properties
        geo_props = scene.geo_node_properties

        row = layout.row(align=True)
        row.label(text=f"V{CURRENT_VERSION[0]}.{CURRENT_VERSION[1]}.{CURRENT_VERSION[2]}")
        row.operator("painterly.set_cycles_render_settings", text="Cycles Settings", icon='RENDER_STILL')


        if addon_props.update_available:
            update_box = layout.box()
            update_box.label(text=f"New Version {addon_props.latest_version} available!", icon='INFO')
            update_box.label(text=f"Changelog: {addon_props.latest_changelog}")
            if addon_props.update_downloaded:
                update_box.operator("painterly.restart_blender", text="Restart Blender", icon='RECOVER_LAST')
            else:
                update_box.operator("painterly.download_update", text="Download Update", icon='IMPORT')

        if not prefs.base_folder_path or not folder_props.folder_configured:
            row = layout.row()
            row.operator("painterly.open_addon_preferences", text="Add-on Preferences", icon='PREFERENCES')
            row = layout.row()
            if not prefs.base_folder_path:
                row.label(text="⚠ Set Painterly asset folder in Prefs.", icon='ERROR')
            else:
                row.label(text="Scanning folders...", icon='INFO')
            return
            
        row = layout.row()
        row.prop(addon_props, "active_mode", expand=True)
        
        if addon_props.active_mode == 'STROKE_PEN':
            
            if bpy.app.version >= (4, 0, 0):
                geo_node_box = layout.box()
                row = geo_node_box.row()
                row.prop(geo_props, "geo_node_mode_enabled", text="Geometry Node Mode", toggle=True, icon='NODETREE')

                if geo_props.geo_node_mode_enabled:
                    active_obj = context.active_object
                    active_primary_stroke = None
                    if active_obj:
                        mod = get_geo_node_modifier(active_obj)
                        if mod:
                            active_primary_stroke = next((ps for ps in geo_props.primary_strokes if ps.obj == active_obj), None)

                    if active_primary_stroke:
                        ps = active_primary_stroke
                        i = -1
                        for idx, p_stroke in enumerate(geo_props.primary_strokes):
                            if p_stroke.obj == ps.obj:
                                i = idx
                                break
                        self.draw_primary_stroke_box(geo_node_box, ps, i, context)
                    else:
                        management_box = geo_node_box.box()
                        col = management_box.column(align=True)
                        col.label(text="Management", icon='TOOL_SETTINGS')
                        col.operator("painterly.add_primary_stroke", text="New Primary from Active", icon='FORCE_CURVE')

                        row = col.row(align=True)
                        row.prop(geo_props, "target_primary_collection", text="Target")
                        row.operator("painterly.instance_stroke", icon='LINKED', text="")

                        geo_node_box.separator()

                        if not geo_props.primary_strokes:
                            geo_node_box.label(text="No Primary Strokes defined.", icon='INFO')
                        
                        for i, ps in enumerate(geo_props.primary_strokes):
                            self.draw_primary_stroke_box(geo_node_box, ps, i, context)
                else:
                    self.draw_legacy_stroke_pen_ui(context)
            else:
                self.draw_legacy_stroke_pen_ui(context)

        elif addon_props.active_mode == 'PAINTERLY_TEXTURE':
            self.draw_painterly_texture_ui(context)

    def draw_primary_stroke_box(self, layout, ps, index, context):
        """Helper to draw the UI box for a single primary stroke."""
        folder_props = context.scene.painterly_folder_properties
        box = layout.box()
        
        header_row = box.row(align=True)
        header_row.alignment = 'LEFT'

        # --- Display Primary Stroke Thumbnail ---
        has_custom_icon = False
        custom_icon_id = 0
        preset_item = get_stroke_preset_item(ps.obj, folder_props)
        if preset_item and preset_item.preview_image:
            if preset_item.preview_image not in custom_icons:
                try: custom_icons.load(preset_item.preview_image, preset_item.preview_filepath, 'IMAGE')
                except: pass
            if preset_item.preview_image in custom_icons:
                custom_icon_id = custom_icons[preset_item.preview_image].icon_id
                has_custom_icon = True
        
        if has_custom_icon:
            header_row.template_icon(custom_icon_id, scale=2.0)
        else:
             op_select = header_row.operator("painterly.select_object", text="", icon='RESTRICT_SELECT_OFF')
             op_select.obj_name = ps.obj.name if ps.obj else ""
        
        if ps.obj:
            header_row.label(text=f"{ps.obj.name}", icon='MOD_CURVE')
        
        op_rem_ps = header_row.operator("painterly.remove_primary_stroke", text="", icon='X')
        op_rem_ps.primary_stroke_index = index

        if ps.obj:
            instance_box = box.box()
            row = instance_box.row(align=True)
            row.alignment = 'LEFT'
            row.label(text=f"Instances ({len(ps.secondary_strokes)})", icon='OBJECT_DATA')
            
            if not ps.secondary_strokes:
                instance_box.label(text="   (Empty)", icon='INFO')
            
            for j, ss in enumerate(ps.secondary_strokes):
                ss_box = instance_box.box()
                ss_header = ss_box.row(align=True)

                # --- Visibility Toggle ---
                if ss.obj:
                    op_vis = ss_header.operator("painterly.toggle_instance_visibility", text="", icon='RESTRICT_VIEW_OFF' if not ss.obj.hide_get() else 'RESTRICT_VIEW_ON', emboss=False)
                    op_vis.obj_name = ss.obj.name
                else:
                    ss_header.label(text="", icon='GHOST_ENABLED')


                # --- Secondary Stroke Thumbnail ---
                has_secondary_icon = False
                secondary_icon_id = 0
                secondary_preset_item = get_stroke_preset_item(ss.obj, folder_props)
                if secondary_preset_item and secondary_preset_item.preview_image:
                    if secondary_preset_item.preview_image not in custom_icons:
                        try: custom_icons.load(secondary_preset_item.preview_image, secondary_preset_item.preview_filepath, 'IMAGE')
                        except: pass
                    if secondary_preset_item.preview_image in custom_icons:
                        secondary_icon_id = custom_icons[secondary_preset_item.preview_image].icon_id
                        has_secondary_icon = True
                
                if has_secondary_icon:
                    ss_header.template_icon(secondary_icon_id, scale=2.0)
                else:
                    ss_header.label(text="", icon='OBJECT_DATA')

                op_sel = ss_header.operator("painterly.select_object", text=ss.obj.name if ss.obj else "INVALID", emboss=False)
                if ss.obj: op_sel.obj_name = ss.obj.name
                
                op_rem = ss_header.operator("painterly.remove_secondary_stroke", text="", icon='X')
                op_rem.primary_stroke_index = index
                op_rem.secondary_stroke_index = j

                ss_controls_box = ss_box.box()
                col = ss_controls_box.column(align=True)
                col.prop(ss, "density")
                col.prop(ss, "scale")
                if not ss.use_align_rotation:
                    col.prop(ss, "rotation_randomness")
                col.prop(ss, "merge_distance")
                
                col.separator()

                if ss.align_rotation_available:
                    align_box = ss_controls_box.box()
                    align_box.prop(ss, "use_align_rotation")
                    if ss.use_align_rotation:
                        align_box.prop(ss, "align_axis", expand=True)
                else:
                    ss_controls_box.label(text="Align Rotation N/A", icon='ERROR')

                transform_box = ss_controls_box.box()
                transform_box.prop(ss, "use_edit_transforms")
                if ss.use_edit_transforms:
                    transform_box.prop(ss, "translation")
                    transform_box.prop(ss, "rotation")
                    transform_box.prop(ss, "scale_transform")


    def draw_legacy_stroke_pen_ui(self, context):
        """Draws the original Stroke Pen UI for legacy versions or when GN Mode is off."""
        layout = self.layout
        stroke_props = context.scene.stroke_brush_properties
        folder_props = context.scene.painterly_folder_properties
        image_scale = 12

        layout.separator()
        layout.prop(stroke_props, "animation_mode", text="Stroke Mode")
        if stroke_props.animation_mode != 'STATIC':
            row = layout.row()
            row.label(text="Step Value:")
            row.prop(stroke_props, "step_value", slider=True)
        cat_box = layout.box()
        cat_box.label(text="Category Selection")
        cat_box.prop(folder_props, "selected_stroke_type", text="Main")
        if folder_props.selected_stroke_type != "ALL":
            cat_box.prop(folder_props, "selected_stroke_subtype", text="Subfolder")
        box = layout.box()
        box.label(text="Stroke Selection")
        row = box.row(align=True)
        row.prop(folder_props, "show_stroke_grid", text="Grid View", toggle=True)
        if folder_props.show_stroke_grid:
            row.prop(folder_props, "previews_per_page", text="Count")
        if folder_props.show_stroke_grid:
            row2 = box.row(align=True)
            op_prev = row2.operator("painterly.navigate_folder", text="<")
            op_prev.folder_type = 'stroke'
            op_prev.direction = 'PREV'
            total = len(folder_props.stroke_folders)
            pg = (folder_props.current_stroke_index // folder_props.previews_per_page) + 1 if total > 0 else 1
            row2.label(text=f"Page {pg}")
            op_next = row2.operator("painterly.navigate_folder", text=">")
            op_next.folder_type = 'stroke'
            op_next.direction = 'NEXT'
            draw_preview_grid(box, folder_props.stroke_folders, folder_props.current_stroke_index, 'stroke', context, image_scale)
        else:
            row2 = box.row(align=True)
            op_prev = row2.operator("painterly.navigate_folder", text="<")
            op_prev.folder_type = 'stroke'
            op_prev.direction = 'PREV'
            if folder_props.stroke_folders:
                idx = folder_props.current_stroke_index
                if idx < len(folder_props.stroke_folders):
                    current_stroke = folder_props.stroke_folders[idx]
                    row2.label(text=current_stroke.name)
                    preview_box = box.box()
                    if current_stroke.preview_image and current_stroke.preview_image not in custom_icons:
                        try:
                            custom_icons.load(current_stroke.preview_image, current_stroke.preview_filepath, 'IMAGE')
                        except:
                            pass
                    if current_stroke.preview_image and current_stroke.preview_image in custom_icons:
                        preview_box.template_icon(icon_value=custom_icons[current_stroke.preview_image].icon_id, scale=image_scale)
            op_next = row2.operator("painterly.navigate_folder", text=">")
            op_next.folder_type = 'stroke'
            op_next.direction = 'NEXT'
        box.operator("object.auto_stroke", text="Add Stroke", icon='PLUS')
        box2 = layout.box()
        box2.label(text="Normal Map Selection")
        rowN = box2.row(align=True)
        rowN.prop(folder_props, "show_normal_grid", text="Grid View", toggle=True)
        if folder_props.show_normal_grid:
            rowN.prop(folder_props, "previews_per_page", text="Count")
        if folder_props.show_normal_grid:
            rowN2 = box2.row(align=True)
            opn_prev = rowN2.operator("painterly.navigate_folder", text="<")
            opn_prev.folder_type = 'normal'
            opn_prev.direction = 'PREV'
            total = len(folder_props.normal_map_folders)
            pg = (folder_props.current_normal_map_index // folder_props.previews_per_page) + 1 if total > 0 else 1
            rowN2.label(text=f"Page {pg}")
            opn_next = rowN2.operator("painterly.navigate_folder", text=">")
            opn_next.folder_type = 'normal'
            opn_next.direction = 'NEXT'
            draw_preview_grid(box2, folder_props.normal_map_folders, folder_props.current_normal_map_index, 'normal', context, image_scale)
        else:
            rowN2 = box2.row(align=True)
            opn_prev = rowN2.operator("painterly.navigate_folder", text="<")
            opn_prev.folder_type = 'normal'
            opn_prev.direction = 'PREV'
            if folder_props.normal_map_folders:
                idx = folder_props.current_normal_map_index
                if idx < len(folder_props.normal_map_folders):
                    current_normal = folder_props.normal_map_folders[idx]
                    rowN2.label(text=current_normal.name)
                    preview_box2 = box2.box()
                    if current_normal.preview_image and current_normal.preview_image not in custom_icons:
                        try:
                            custom_icons.load(current_normal.preview_image, current_normal.preview_filepath, 'IMAGE')
                        except:
                            pass
                    if current_normal.preview_image and current_normal.preview_image in custom_icons:
                        preview_box2.template_icon(icon_value=custom_icons[current_normal.preview_image].icon_id, scale=image_scale)
            opn_next = rowN2.operator("painterly.navigate_folder", text=">")
            opn_next.folder_type = 'normal'
            opn_next.direction = 'NEXT'
        layout.prop(stroke_props, "normal_map_strength", text="Normal Map Strength", slider=True)
        if stroke_props.use_secondary_color:
            mixer_box = layout.box()
            mixer_box.label(text="Color Mixer")
            mixer_box.prop(stroke_props, "color_mixer_offset", slider=True)
        color_box = layout.box()
        color_box.label(text="Colors")
        color_box.prop(stroke_props, "color", text="Base Color")
        color_box.prop(stroke_props, "use_secondary_color")
        if stroke_props.use_secondary_color:
            color_box.prop(stroke_props, "secondary_color", text="Secondary")
            rowC3 = color_box.row()
            rowC3.operator("painterly.add_additional_color_secondary", text="Add Additional Secondary Color", icon='ADD')
            for i, ac in enumerate(stroke_props.additional_secondary_colors):
                rowC4 = color_box.row(align=True)
                rowC4.prop(ac, "color", text=f"Sec {i+1}")
                rem2 = rowC4.operator("painterly.remove_additional_color_secondary", text="", icon='X')
                rem2.index = i
        color_box.prop(stroke_props, "metallic", slider=True)
        color_box.prop(stroke_props, "roughness", slider=True)
        color_box.prop(stroke_props, "emission", slider=True)
        subsurf_box = layout.box()
        subsurf_box.label(text="Subsurface Controls")
        subsurf_box.prop(stroke_props, "subsurface_amount", text="Weight", slider=True)
        subsurf_box.prop(stroke_props, "subsurface_radius", text="Radius")
        subsurf_box.prop(stroke_props, "subsurface_scale", slider=True)
        tilt_box = layout.box()
        tilt_box.label(text="Tilt Controls")
        tilt_box.prop(stroke_props, "global_tilt", slider=True)
        tilt_box.prop(stroke_props, "maintain_tilt")
        if stroke_props.maintain_tilt:
            tilt_box.prop(stroke_props, "mean_tilt", slider=True)
        alpha_box = layout.box()
        alpha_box.label(text="Alpha Channel")
        alpha_box.prop(stroke_props, "use_alpha_channel", text="Use Alpha Channel")
        extr_box = layout.box()
        extr_box.label(text="3D Extrusion")
        if stroke_props.lock_depth_to_extrusion:
            extr_box.prop(stroke_props, "extrusion_locked", slider=True)
        else:
            extr_box.prop(stroke_props, "extrusion", slider=True)
        extr_box.prop(stroke_props, "lock_depth_to_extrusion")
        if not stroke_props.lock_depth_to_extrusion:
            extr_box.prop(stroke_props, "depth", slider=True)
        
        solidify_box = layout.box()
        solidify_box.label(text="Solidify")
        solidify_box.prop(stroke_props, "use_solidify", text="Enable Solidify")
        if stroke_props.use_solidify:
            solidify_box.prop(stroke_props, "solidify_thickness")
            solidify_box.prop(stroke_props, "solidify_offset", slider=True)

        disp_box = layout.box()
        disp_box.label(text="Displacement")
        disp_box.prop(stroke_props, "displacement_height", text="Height", slider=True)
        disp_box.prop(stroke_props, "displacement_midlevel", text="Midlevel", slider=True)
        disp_box.prop(stroke_props, "displacement_scale", text="Scale", slider=True)
        
        eff_box = layout.box()
        eff_box.label(text="Effects")
        eff_box.prop(stroke_props, "effect_type", text="")
        if stroke_props.effect_type != EFFECT_NONE:
            col = eff_box.column(align=True)
            col.label(text="Color/Alpha Vector Input:")
            col.prop(stroke_props, "effect_color_vec_mode", text="")
            col.label(text="Normal Map Vector Input:")
            col.prop(stroke_props, "effect_normal_vec_mode", text="")
            if stroke_props.effect_type == EFFECT_MAGIC:
                eff_box.label(text="Magic Texture Controls")
                eff_box.prop(stroke_props, "effect_magic_scale", slider=True)
                eff_box.prop(stroke_props, "effect_magic_distortion", slider=True)
                eff_box.prop(stroke_props, "effect_magic_depth")
            elif stroke_props.effect_type == EFFECT_VORONOI:
                eff_box.label(text="Voronoi Texture Controls")
                eff_box.prop(stroke_props, "effect_voronoi_scale", slider=True)
                eff_box.prop(stroke_props, "effect_voronoi_smoothness", slider=True)
                eff_box.prop(stroke_props, "effect_voronoi_exponent", slider=True)
                eff_box.prop(stroke_props, "effect_voronoi_randomness", slider=True)
                eff_box.prop(stroke_props, "effect_voronoi_feature", text="Feature")
                eff_box.prop(stroke_props, "effect_voronoi_distance", text="Distance")
            elif stroke_props.effect_type == EFFECT_NOISE:
                eff_box.label(text="Noise Texture Controls")
                eff_box.prop(stroke_props, "effect_noise_scale", slider=True)
                eff_box.prop(stroke_props, "effect_noise_detail", slider=True)
                eff_box.prop(stroke_props, "effect_noise_roughness", slider=True)
                eff_box.prop(stroke_props, "effect_noise_distortion", slider=True)
        
        # --- NEW: Wave Modifier UI ---
        eff_box.separator()
        obj = context.active_object
        mod = None
        if obj and obj.type == 'CURVE':
            mod = obj.modifiers.get("Painterly_Wave")
        
        if mod:
            eff_box.operator("painterly.toggle_wave_modifier", text="Remove Wave Modifier", icon='X')
            wave_box = eff_box.box()
            row = wave_box.row()
            row.prop(stroke_props, "wave_motion_y", text="Y")
            row.prop(stroke_props, "wave_motion_x", text="X")
            wave_box.prop(stroke_props, "wave_height", slider=True)
            wave_box.prop(stroke_props, "wave_width", slider=True)
            wave_box.prop(stroke_props, "wave_narrowness", slider=True)
            wave_box.prop(stroke_props, "wave_speed", slider=True)
        else:
            eff_box.operator("painterly.toggle_wave_modifier", text="Add Wave Modifier", icon='MOD_WAVE')

        extra_box = layout.box()
        extra_box.label(text="Extras")
        extra_box.prop(stroke_props, "add_subdivision")
        extra_box.prop(stroke_props, "optimized_viewport_strokes")
        layout.operator("painterly.open_addon_preferences", text="Add-on Preferences", icon='PREFERENCES')


    def draw_painterly_texture_ui(self, context):
        layout = self.layout
        folder_props = context.scene.painterly_folder_properties
        stylized_props = context.scene.stylized_painterly_properties
        image_scale = 12

        p_box = layout.box()
        p_box.label(text="Preset Selection")
        row = p_box.row(align=True)
        row.prop(folder_props, "show_preset_grid", text="Grid View", toggle=True)
        if folder_props.show_preset_grid:
            row.prop(folder_props, "previews_per_page", text="Count")
        if folder_props.show_preset_grid:
            row2 = p_box.row(align=True)
            op_prev = row2.operator("painterly.navigate_folder", text="<")
            op_prev.folder_type = 'preset'
            op_prev.direction = 'PREV'
            total = len(folder_props.preset_folders)
            pg = (folder_props.current_preset_index // folder_props.previews_per_page) + 1 if total > 0 else 1
            row2.label(text=f"Page {pg}")
            op_next = row2.operator("painterly.navigate_folder", text=">")
            op_next.folder_type = 'preset'
            op_next.direction = 'NEXT'
            draw_preview_grid(p_box, folder_props.preset_folders, folder_props.current_preset_index, 'preset', context, image_scale)
        else:
            row2 = p_box.row(align=True)
            op_prev = row2.operator("painterly.navigate_folder", text="<")
            op_prev.folder_type = 'preset'
            op_prev.direction = 'PREV'
            if folder_props.preset_folders:
                idx = folder_props.current_preset_index
                if idx < len(folder_props.preset_folders):
                    cpres = folder_props.preset_folders[idx]
                    row2.label(text=cpres.name)
                    if cpres.preview_image and cpres.preview_image not in custom_icons:
                        try:
                            custom_icons.load(cpres.preview_image, cpres.preview_filepath, 'IMAGE')
                        except:
                            pass
                    if cpres.preview_image and cpres.preview_image in custom_icons:
                        preview_box = p_box.box()
                        preview_box.template_icon(icon_value=custom_icons[cpres.preview_image].icon_id, scale=image_scale)
            op_next = row2.operator("painterly.navigate_folder", text=">")
            op_next.folder_type = 'preset'
            op_next.direction = 'NEXT'
        layout.operator("texture.auto_bake")
        layout.prop(stylized_props, "image")
        layout.prop(stylized_props, "random_seed")
        layout.prop(stylized_props, "batch_mode", text="Batch Mode")
        if stylized_props.batch_mode:
            layout.prop(stylized_props, "batch_folder", text="Output Folder")
            layout.prop(stylized_props, "batch_amount")
        if not check_pillow():
            layout.operator("painterly.install_dependencies", text="Install Dependencies (PIL)", icon='IMPORT')
        else:
            layout.operator("texture.apply_painterly_effect", text="Apply Painterly Effect", icon='PLUS')
        layout.label(text="May take up to 1 minute", icon='INFO')

def draw_preview_grid(layout, folder_collection, current_index, folder_type, context, image_scale):
    global custom_icons
    props = context.scene.painterly_folder_properties
    grid_flow = layout.grid_flow(row_major=True, columns=2, even_columns=True, even_rows=True, align=True)
    start = (current_index // props.previews_per_page) * props.previews_per_page
    end = min(start + props.previews_per_page, len(folder_collection))
    for idx in range(start, end):
        item = folder_collection[idx]
        box = grid_flow.box()
        box.label(text=item.name)
        pbox = box.box()
        if item.preview_image and item.preview_image not in custom_icons:
            try:
                custom_icons.load(item.preview_image, item.preview_filepath, 'IMAGE')
            except:
                pass
        if item.preview_image and item.preview_image in custom_icons:
            pbox.template_icon(icon_value=custom_icons[item.preview_image].icon_id, scale=image_scale)
        op = box.operator("painterly.select_preview", text="Select")
        op.folder_type = folder_type
        op.index = idx

classes_to_register = [
    PAINTERLY_OT_install_dependencies,
    PAINTERLY_OT_save_preferences,
    PAINTERLY_OT_open_feedback,
    PAINTERLY_OT_open_youtube,
    PainterlyAddonPreferences,
    OpenAddonPreferencesOperator,
    SetCyclesRenderSettings,
    AdditionalColor,
    PAINTERLY_OT_AddAdditionalColorSecondary,
    PAINTERLY_OT_RemoveAdditionalColorSecondary,
    FolderItem,
    PainterlyFolderProperties,
    AddonProperties,
    GeoNodeSecondaryStroke,
    GeoNodePrimaryStroke,
    GeoNodeProperties,
    StrokeBrushProperties,
    PainterlyProperties,
    PAINTERLY_OT_AddPrimaryStroke,
    PAINTERLY_OT_InstanceStroke,
    PAINTERLY_OT_RemovePrimaryStroke,
    PAINTERLY_OT_RemoveSecondaryStroke,
    PAINTERLY_OT_SelectObject,
    PAINTERLY_OT_ToggleInstanceVisibility,
    CheckForUpdatesOperator,
    DownloadUpdateOperator,
    RestartBlenderOperator,
    RefreshFoldersOperator,
    SetFolderOperator,
    NavigateFolderOperator,
    SelectPreviewOperator,
    SelectObjectOperator,
    StartMaintainingTiltOperator,
    StopMaintainingTiltOperator,
    AutoStrokeOperator,
    AutoBakeOperator,
    PainterlyEffectOperator,
    AddDisplacementOperator,
    StrokeBrushPanel,
    RefreshPreviewsOperator,
    PAINTERLY_OT_ToggleWaveModifier,
]


def register():
    global custom_icons
    custom_icons = bpy.utils.previews.new()
    
    bpy.types.WindowManager.painterly_color_swatch = FloatVectorProperty(
        name="Color Swatch", subtype='COLOR', size=4
    )
    
    for cls in classes_to_register:
        bpy.utils.register_class(cls)

    bpy.types.Scene.painterly_folder_properties = PointerProperty(type=PainterlyFolderProperties)
    bpy.types.Scene.addon_properties = PointerProperty(type=AddonProperties)
    bpy.types.Scene.stroke_brush_properties = PointerProperty(type=StrokeBrushProperties)
    bpy.types.Scene.stylized_painterly_properties = PointerProperty(type=PainterlyProperties)
    bpy.types.Scene.geo_node_properties = PointerProperty(type=GeoNodeProperties)

    # --- CORRECTED AUTO-DETECT ---
    try:
        addon_prefs_owner = bpy.context.preferences.addons.get(get_addon_key())
        if addon_prefs_owner:
            prefs = addon_prefs_owner.preferences
            if not prefs.base_folder_path:
                auto_root = os.path.dirname(os.path.abspath(__file__))
                prefs.base_folder_path = auto_root
                print("[Painterly] Auto-set root folder →", auto_root)
    except Exception as exc:
        print("[Painterly] auto-detect failed during register:", exc)
    
    if painterly_load_post_handler not in bpy.app.handlers.load_post:
        bpy.app.handlers.load_post.append(painterly_load_post_handler)
    if painterly_frame_change_post not in bpy.app.handlers.frame_change_post:
        bpy.app.handlers.frame_change_post.append(painterly_frame_change_post)

def unregister():
    global custom_icons

    if painterly_frame_change_post in bpy.app.handlers.frame_change_post:
        bpy.app.handlers.frame_change_post.remove(painterly_frame_change_post)
    if painterly_load_post_handler in bpy.app.handlers.load_post:
        bpy.app.handlers.load_post.remove(painterly_load_post_handler)
    
    if custom_icons:
        bpy.utils.previews.remove(custom_icons)
        custom_icons = None
    
    try:
        del bpy.types.Scene.stylized_painterly_properties
        del bpy.types.Scene.stroke_brush_properties
        del bpy.types.Scene.addon_properties
        del bpy.types.Scene.painterly_folder_properties
        del bpy.types.Scene.geo_node_properties
        
        if hasattr(bpy.types.WindowManager, 'painterly_color_swatch'):
            del bpy.types.WindowManager.painterly_color_swatch
    except (AttributeError, RuntimeError):
        pass

    for cls in reversed(classes_to_register):
        if hasattr(bpy.utils, 'unregister_class'):
            try:
                bpy.utils.unregister_class(cls)
            except RuntimeError:
                pass

if __name__ == "__main__":
    register()