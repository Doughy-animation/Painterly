bl_info = {
    "name": "Painterly",
    "author": "Patrick Daugherty - Doughy Animation Studio",
    "version": (2, 5, 0), # Version updated to reflect major changes
    "blender": (2, 9, 3),
    "location": "View3D > Sidebar > Painterly",
    "description": ("Stylized painterly strokes and textures with GPU acceleration and a real-time proxy workflow. "
                    "Create painterly strokes and normal map textures using handcrafted textures. Includes Geometry Node Mode."),
    "category": "3D View",
    "doc_url": "https://www.doughyanimation.com/painterly",
}

# Global version constant for UI display
CURRENT_VERSION = (2, 5, 0)

# URL for checking updates
UPDATE_JSON_URL = (
    "https://raw.githubusercontent.com/Doughy-animation/Painterly/main/UPDATE_LATEST.JSON"
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

# --- NEW: GPU Acceleration & Renderer Backend ---
try:
    import cupy as cp
    from cupyx.scipy.ndimage import affine_transform
    CUPY_AVAILABLE = True
    print("[Painterly] CuPy found. GPU acceleration is available.")
except ImportError:
    cp = None
    affine_transform = None
    CUPY_AVAILABLE = False
    print("[Painterly] CuPy not found. Using CPU fallback for rendering.")


# -------------------------------------------------------------------------
# Helper utilities
# -------------------------------------------------------------------------
def get_addon_key() -> str:
    """Return the module-name Blender registered this file under."""
    return __name__

def _obj_alive(obj) -> bool:
    """Return True if 'obj' is a still-alive bpy.data.objects entry."""
    try:
        return (obj is not None) and (obj.name in bpy.data.objects)
    except ReferenceError:
        return False

def _safe_data_update(obj):
    """Safely call obj.data.update() if it's present and valid."""
    try:
        data = getattr(obj, "data", None)
        upd = getattr(data, "update", None)
        if callable(upd):
            upd()
    except ReferenceError:
        pass

def check_pillow() -> bool:
    import site
    user_site = site.getusersitepackages()
    if user_site not in sys.path:
        sys.path.append(user_site)
    try:
        import PIL
        from PIL import Image, ImageDraw, ImageFilter
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
# MIGRATION & REPAIR
# ---------------------------
def _ensure_frame_count_on_material(mat):
    """Recalculates and sets the 'frame_count' custom property if missing."""
    if not mat or "frame_count" in mat:
        return
    nt = getattr(mat, "node_tree", None)
    if not nt:
        return
    # Count frames by a reliable node naming convention
    count = sum(1 for n in nt.nodes if n.name.startswith("StrokeBSDF_"))
    if count > 0:
        mat["frame_count"] = count

def _repair_painterly_drivers_after_update(scene):
    """
    Finds old, unsafe driver expressions in materials and replaces them
    with a hardened version to prevent division-by-zero errors on reload.
    """
    fixed_count = 0
    for mat in bpy.data.materials:
        if not mat.name.startswith("Painterly_"):
            continue

        _ensure_frame_count_on_material(mat)

        nt = getattr(mat, "node_tree", None)
        if not nt or not nt.animation_data:
            continue
            
        for fcu in list(nt.animation_data.drivers or []):
            drv = fcu.driver
            if not drv or not drv.expression:
                continue
                
            original_expr = drv.expression
            repaired_expr = original_expr
            
            # Harden against step=0
            if "/ step" in repaired_expr and "max(step, 1)" not in repaired_expr:
                repaired_expr = repaired_expr.replace("/ step", "/ max(step, 1)")

            # Harden against fc=0 or fc being missing
            if "% fc" in repaired_expr and "max(fc, 1)" not in repaired_expr:
                 repaired_expr = repaired_expr.replace("% fc", "% max(fc, 1)")
                 
            if repaired_expr != original_expr:
                drv.expression = repaired_expr
                fixed_count += 1

                # Ensure all variables exist and are correctly targeted
                vars = {v.name: v for v in drv.variables}
                
                if "frame" not in vars:
                    v = drv.variables.new(); v.name = "frame"
                else:
                    v = vars["frame"]
                v.targets[0].id_type = 'SCENE'; v.targets[0].id = scene; v.targets[0].data_path = "frame_current"

                if "step" not in vars:
                    v = drv.variables.new(); v.name = "step"
                else:
                    v = vars["step"]
                v.targets[0].id_type = 'SCENE'; v.targets[0].id = scene; v.targets[0].data_path = "stroke_brush_properties.step_value"

                if "fc" not in vars:
                    v = drv.variables.new(); v.name = "fc"
                else:
                    v = vars["fc"]
                v.targets[0].id_type = 'MATERIAL'; v.targets[0].id = mat; v.targets[0].data_path = '["frame_count"]'
                    
    if fixed_count > 0:
        print(f"[Painterly] Repaired {fixed_count} outdated material drivers in the scene.")

# ---------------------------
# GLOBALS & DEBOUNCE VARIABLES
# ---------------------------
last_color_update_time = 0.0
DEBOUNCE_INTERVAL = 0.1
DEBOUNCE_TOTAL_DELAY = 0.2
_in_update_color = False

# ---------------------------
# Robust ramp-update queue
# ---------------------------
pending_inactive_ramp_refs = []  # list of (material_name, node_name)
_timer_registered = False


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

def sync_combined_preset_list(context):
    """
    Clears and repopulates the preset_selections list to match the
    discovered preset folders from both Painterly Texture and Stroke Pen modes.
    Preserves selection state where possible.
    """
    folder_props = context.scene.painterly_folder_properties
    stylized_props = context.scene.stylized_painterly_properties

    old_selections = {item.path for item in stylized_props.preset_selections if item.selected}
    stylized_props.preset_selections.clear()

    for preset_folder in folder_props.preset_folders:
        item = stylized_props.preset_selections.add()
        item.name = f"[Texture] {preset_folder.name}"
        item.path = preset_folder.path
        if item.path in old_selections:
            item.selected = True

    if stylized_props.include_stroke_pen_alphas:
        for stroke_type_folder in folder_props.stroke_type_folders:
            item = stylized_props.preset_selections.add()
            item.name = f"[Stroke Pen] {stroke_type_folder.name} (All)"
            item.path = stroke_type_folder.path
            if item.path in old_selections:
                item.selected = True
        
        for stroke_type_folder in folder_props.stroke_type_folders:
            for sub_name in os.listdir(stroke_type_folder.path):
                 sub_path = os.path.join(stroke_type_folder.path, sub_name)
                 if os.path.isdir(sub_path) and sub_name.lower() != "ui_image":
                    item = stylized_props.preset_selections.add()
                    item.name = f"[Stroke Pen] {stroke_type_folder.name} > {sub_name}"
                    item.path = sub_path
                    if item.path in old_selections:
                        item.selected = True


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

    for main_item in props.stroke_type_folders:
        scan_directory_recursive(main_item.path, props.stroke_folders)
    
    sync_combined_preset_list(context)
    
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
    bl_label  = "Install Dependencies (PIL & CuPy)"
    bl_description = "Installs Pillow for image processing and CuPy for GPU acceleration (NVIDIA only)"

    def execute(self, context):
        try:
            # Install Pillow
            self.report({'INFO'}, "Installing Pillow for image processing...")
            subprocess.check_call([sys.executable, "-m", "ensurepip", "--default-pip"])
            cmd_pillow = [sys.executable, "-m", "pip", "install", "Pillow"]
            if platform.system() == "Windows":
                cmd_pillow.insert(4, "--user")
            subprocess.check_call(cmd_pillow)
            self.report({'INFO'}, "Pillow installed successfully!")
            
            # Attempt to install CuPy
            self.report({'INFO'}, "Attempting to install CuPy for GPU acceleration. This may take several minutes...")
            # Let pip figure out the correct CUDA version. Using "cupy-cuda11x" is a safe bet for modern Blender versions.
            cmd_cupy = [sys.executable, "-m", "pip", "install", "cupy-cuda11x"]
            if platform.system() == "Windows":
                cmd_cupy.insert(4, "--user")
            try:
                subprocess.check_call(cmd_cupy)
                self.report({'INFO'}, "CuPy installed successfully! GPU acceleration is available.")
            except subprocess.CalledProcessError:
                self.report({'WARNING'}, "CuPy installation failed. This is expected if you don't have a compatible NVIDIA GPU or CUDA Toolkit. Addon will use CPU fallback.")

            # Invalidate caches and set flag
            import site
            importlib.reload(site)
            user_site = site.getusersitepackages()
            if user_site not in sys.path:
                sys.path.append(user_site)
            importlib.invalidate_caches()
            addon = context.preferences.addons.get(get_addon_key())
            if addon:
                addon.preferences.dependencies_installed = True

            return {'FINISHED'}
        except Exception as e:
            self.report({'ERROR'}, f"An error occurred during installation: {e}")
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

    base_folder_path: StringProperty(
        name="Base Folder Path",
        subtype='DIR_PATH',
        description="Folder that holds all Painterly assets",
        update=lambda self, ctx: _mirror_path_to_scene(self, ctx)
    )
    dependencies_installed: BoolProperty(name="Dependencies Installed", default=False)
    enable_auto_update:     BoolProperty(name="Enable Automatic Updates", default=True)

    def draw(self, context):
        layout = self.layout
        props = context.scene.addon_properties 
        col = layout.column(align=True)

        col.prop(self, "base_folder_path")
        if self.base_folder_path:
            col.label(text="Folder set and saved ✔", icon='CHECKMARK')
        else:
            col.label(text="Not set – Painterly UI is hidden ⛔", icon='ERROR')
        col.operator("painterly.save_preferences", icon='FILE_TICK')

        box_deps = col.box()
        box_deps.label(text="Dependencies", icon='SCRIPTPLUGINS')
        if check_pillow():
            box_deps.label(text="Pillow (CPU): Installed ✔", icon='CHECKMARK')
        else:
            box_deps.label(text="Pillow (CPU): Not Installed ⛔", icon='ERROR')
        
        if CUPY_AVAILABLE:
            box_deps.label(text="CuPy (GPU): Installed ✔", icon='CHECKMARK')
        else:
            box_deps.label(text="CuPy (GPU): Not Installed", icon='INFO')
        
        box_deps.operator("painterly.install_dependencies", icon='CONSOLE')


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

        row = col.row(align=True)
        row.operator("painterly.open_feedback", icon='HELP')
        row.operator("painterly.open_youtube",  icon='URL')


# ----- NEW COLOR MIXER CODE START -----

def schedule_inactive_ramp_updates(context):
    """Register a single-shot timer if not already registered."""
    global _timer_registered
    try:
        if not _timer_registered or not bpy.app.timers.is_registered(debounce_update_inactive_ramp_nodes):
            _timer_registered = True
            bpy.app.timers.register(debounce_update_inactive_ramp_nodes, first_interval=DEBOUNCE_TOTAL_DELAY)
    except Exception as e:
        print("schedule_inactive_ramp_updates error:", e)


def debounce_update_inactive_ramp_nodes():
    """
    Fire after the user stops dragging sliders for DEBOUNCE_TOTAL_DELAY.
    Drain the whole queue in one go, re-resolving nodes by (material_name, node_name).
    Stop the timer when done.
    """
    global last_color_update_time, pending_inactive_ramp_refs, _timer_registered

    try:
        # Keep waiting while the user is still interacting.
        if time.time() - last_color_update_time < DEBOUNCE_TOTAL_DELAY:
            return DEBOUNCE_INTERVAL  # keep deferring

        # Drain the queue atomically
        while pending_inactive_ramp_refs:
            mat_name, node_name = pending_inactive_ramp_refs.pop(0)

            mat = bpy.data.materials.get(mat_name)
            if not mat or not mat.node_tree:
                continue

            node = mat.node_tree.nodes.get(node_name)
            if node and node.type == 'VALTORGB':
                update_ramp_node(node)

    except Exception as e:
        print("Error in debounce_update_inactive_ramp_nodes:", e)

    # Done; turn the timer off
    _timer_registered = False
    return None  # stop the timer

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
    global _in_update_color, last_color_update_time, pending_inactive_ramp_refs
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
        pending_inactive_ramp_refs.clear()
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
                            # Queue a stable reference we can resolve later
                            pending_inactive_ramp_refs.append((mat.name, node.name))
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

def refresh_all_painterly_strokes(context):
    """
    On file load or addon reload, iterates through all Painterly strokes
    and reapplies crucial material settings to prevent glitches.
    """
    for obj in bpy.data.objects:
        if obj.name.startswith("Painterly_") and obj.type == 'CURVE' and obj.active_material:
            override_context = context.copy()
            override_context['object'] = obj
            
            update_material_properties(override_context)
            update_alpha_channel(override_context)

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
    stroke_props = context.scene.stroke_brush_properties
    animation_mode = stroke_props.animation_mode

    if self.stroke_type_folders:
        for i, folder in enumerate(self.stroke_type_folders):
            is_static_folder = folder.name.endswith(" - Static")
            
            # If in animated mode, skip static folders
            if animation_mode == 'ANIMATED' and is_static_folder:
                continue
            
            # Prepare display name and icon
            display_name = folder.name
            icon = 'NONE'
            if is_static_folder:
                display_name = folder.name.removesuffix(" - Static").strip()
                icon = 'STAR'
                
            items.append((str(i), display_name, f"Select {display_name} category", icon, i + 1))

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
    """Finds the Painterly Geometry Nodes modifier on an object (safe)."""
    try:
        if not _obj_alive(obj):
            return None
        for mod in obj.modifiers:
            if getattr(mod, "type", None) == 'NODES':
                ng = getattr(mod, "node_group", None)
                if ng and getattr(ng, "name", "").startswith("Painterly_GN_"):
                    return mod
    except ReferenceError:
        return None
    return None

def _secondary_safe_name(obj_name: str) -> str:
    import re
    return re.sub(r'[^\w\s-]', '', obj_name).replace(' ', '_')

def _get_instance_nodes(ng, secondary_name):
    """Return (dist_node, group_input_node, links) for this instance."""
    dist = ng.nodes.get(f"Distribute_{secondary_name}")
    n_in = ng.nodes.get("Group Input")
    return dist, n_in, ng.links if ng else (None, None, None)

def _set_density_factor_link(ng, ss_prop, secondary_name, connect: bool):
    """
    connect=True  -> ensure Group Input socket -> Distribute.Density Factor link exists
    connect=False -> remove that link and set the socket's default to 1.0
    Works across Blender versions ("Density Factor" vs "Density").
    """
    if not ng or not ss_prop or not ss_prop.density_mask_socket_identifier:
        return
    dist, n_in, links = _get_instance_nodes(ng, secondary_name)
    if not (dist and n_in):
        return

    target_input = dist.inputs.get("Density Factor") or dist.inputs.get("Density")
    if not target_input:
        return

    # Remove existing links to that input (if any)
    for lnk in list(links):
        if lnk.to_node == dist and lnk.to_socket == target_input:
            links.remove(lnk)

    if connect:
        # Recreate link from the correct Group Input socket by identifier
        out = next((s for s in n_in.outputs if s.identifier == ss_prop.density_mask_socket_identifier), None)
        if out:
            links.new(out, target_input)
    else:
        # When disconnected, make sure we default to 1.0 (full density)
        try:
            target_input.default_value = 1.0
        except Exception:
            pass

def _force_gn_refresh(obj):
    """Nudge Blender to re-evaluate GeoNodes after modifier/links change."""
    try:
        if not _obj_alive(obj):
            return
        mod = get_geo_node_modifier(obj)
        if not mod:
            return

        # Toggle viewport flag to force depsgraph recalc
        vis = mod.show_viewport
        mod.show_viewport = False
        mod.show_viewport = vis

        obj.update_tag()
        _safe_data_update(obj)
    except ReferenceError:
        # Under deletion / undo, silently ignore
        return

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
    n_in.name = "Group Input"
    n_in.location = (-300, 0)
    
    n_out = ng.nodes.new("NodeGroupOutput")
    n_out.location = (600, 0)
    
    n_setmat = ng.nodes.new("GeometryNodeSetMaterial")
    n_setmat.name = "Painterly_Set_Material"
    n_setmat.location = (0, -150)
    if primary_stroke_object.active_material:
        n_setmat.inputs["Material"].default_value = primary_stroke_object.active_material
    
    n_join = ng.nodes.new("GeometryNodeJoinGeometry")
    n_join.name = "Painterly_Join"
    n_join.location = (300, 0)

    ng.links.new(n_in.outputs["Geometry"], n_setmat.inputs["Geometry"])
    ng.links.new(n_setmat.outputs["Geometry"], n_join.inputs[0])
    ng.links.new(n_join.outputs["Geometry"], n_out.inputs["Geometry"])

    mod = primary_stroke_object.modifiers.new(name="Painterly Geo Nodes", type='NODES')
    mod.node_group = ng
    
    # If a wave modifier exists, move the new GN modifier below it.
    wave_mod = primary_stroke_object.modifiers.get("Painterly_Wave")
    if wave_mod:
        wave_mod_index = primary_stroke_object.modifiers.find("Painterly_Wave")
        if wave_mod_index != -1:
            bpy.ops.object.modifier_move_to_index(modifier=mod.name, index=wave_mod_index + 1)

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
        if _obj_alive(ps.obj):
            items.append((str(i), ps.obj.name, f"Instance to '{ps.obj.name}'"))
    return items

def update_geo_node_instance_values(self, context):
    """Directly updates the values of named nodes within a specific instance branch."""
    # Find owning primary/secondary safely
    primary_stroke = None
    secondary_stroke_prop = None
    try:
        for ps in context.scene.geo_node_properties.primary_strokes:
            for ss in ps.secondary_strokes:
                if ss.as_pointer() == self.as_pointer():
                    primary_stroke = ps
                    secondary_stroke_prop = ss
                    break
            if primary_stroke:
                break
    except ReferenceError:
        return

    # Validate objects
    if not primary_stroke or not _obj_alive(primary_stroke.obj):
        return
    if not secondary_stroke_prop or not _obj_alive(secondary_stroke_prop.obj):
        return

    mod = get_geo_node_modifier(primary_stroke.obj)
    if not mod or not getattr(mod, "node_group", None):
        return

    ng = mod.node_group
    nodes = ng.nodes
    
    secondary_name = re.sub(r'[^\w\s-]', '', secondary_stroke_prop.obj.name).replace(' ', '_')
    
    dist_node = nodes.get(f"Distribute_{secondary_name}")
    scale_node = nodes.get(f"Scale_{secondary_name}")
    rot_node = nodes.get(f"Rotation_{secondary_name}")
    merge_node = nodes.get(f"Merge_{secondary_name}")
    transform_node = nodes.get(f"Transform_{secondary_name}")
    align_rot_node = nodes.get(f"AlignRotation_{secondary_name}")
    switch_node = nodes.get(f"SwitchRotation_{secondary_name}")

    if dist_node: dist_node.inputs["Density Max"].default_value = self.density
    if scale_node: scale_node.inputs["Max"].default_value = self.scale
    if rot_node: rot_node.inputs["Max"].default_value = (self.rotation_randomness * math.pi * 2, self.rotation_randomness * math.pi * 2, self.rotation_randomness * math.pi * 2)
    if merge_node: merge_node.inputs["Distance"].default_value = self.merge_distance
    
    if transform_node:
        transform_node.inputs['Translation'].default_value = self.translation
        transform_node.inputs['Rotation'].default_value = self.rotation
        transform_node.inputs['Scale'].default_value = self.scale_transform

    if align_rot_node:
        if hasattr(align_rot_node, 'rotation_type'):
            align_rot_node.rotation_type = self.align_axis + '_AXIS'
        elif hasattr(align_rot_node, 'axis'):
            align_rot_node.axis = self.align_axis
        
    if switch_node:
        switch_node.inputs['Switch'].default_value = self.use_align_rotation

    if not self.density_mask_socket_identifier and _obj_alive(primary_stroke.obj):
        mod = get_geo_node_modifier(primary_stroke.obj)
        if mod and mod.node_group and _obj_alive(self.obj):
            safe_obj_name = re.sub(r'[^\w\s-]', '', self.obj.name).replace(' ', '_')
            expected_name = f"Density Mask {safe_obj_name}"
            for item in mod.node_group.interface.items_tree:
                if getattr(item, "name", "") == expected_name:
                    self.density_mask_socket_identifier = item.identifier
                    break

    # --- DENSITY MASK: modifier keys + live link management + refresh ---
    if self.density_mask_socket_identifier:
        # Re-find primary stroke safely, as it could have changed
        current_primary_stroke = None
        try:
            for ps in context.scene.geo_node_properties.primary_strokes:
                for ss in ps.secondary_strokes:
                    if ss.as_pointer() == self.as_pointer():
                        current_primary_stroke = ps
                        break
                if current_primary_stroke:
                    break
        except ReferenceError:
            return

        if not current_primary_stroke or not _obj_alive(current_primary_stroke.obj):
            return

        mod = get_geo_node_modifier(current_primary_stroke.obj)
        ng = mod.node_group if (mod and mod.node_group) else None

        key_use  = f"{self.density_mask_socket_identifier}_use_attribute"
        key_name = f"{self.density_mask_socket_identifier}_attribute_name"

        vg_is_valid = False
        if self.use_density_mask and self.density_vertex_group:
            obj = current_primary_stroke.obj
            vg_is_valid = (obj.type == 'MESH') and (self.density_vertex_group in {vg.name for vg in obj.vertex_groups})

        if mod:
            if vg_is_valid:
                mod[key_use]  = True
                mod[key_name] = self.density_vertex_group
            else:
                mod[key_use] = False
                if key_name in mod:
                    try:
                        del mod[key_name]
                    except TypeError:
                        pass
        
        if ng and _obj_alive(self.obj):
            sec_name = _secondary_safe_name(self.obj.name)
            _set_density_factor_link(ng, self, sec_name, connect=(self.use_density_mask and vg_is_valid))

        if current_primary_stroke and _obj_alive(current_primary_stroke.obj):
            _force_gn_refresh(current_primary_stroke.obj)
            
    return None

class GeoNodeSecondaryStroke(PropertyGroup):
    """Properties for a single secondary (instanced) stroke."""
    name: StringProperty(name="Name")
    obj: PointerProperty(type=bpy.types.Object, name="Secondary Stroke Object")
    
    density: FloatProperty(name="Density Max", default=10.0, min=0.0, max=1000.0, update=update_geo_node_instance_values, step=10)
    scale: FloatProperty(name="Scale", description="Controls the maximum random scale of instances", default=1.0, min=0.0, max=50.0, update=update_geo_node_instance_values, step=1)
    rotation_randomness: FloatProperty(name="Rotation", default=1.0, min=0.0, max=1.0, update=update_geo_node_instance_values, description="Controls the maximum random rotation on all axes")
    merge_distance: FloatProperty(name="Merge Distance", default=0.0, min=0.0, max=10.0, update=update_geo_node_instance_values, step=1, precision=3)

    use_density_mask: BoolProperty(name="Use Density Mask", default=False, update=update_geo_node_instance_values, description="Use a vertex group from the primary object to control instance density")
    density_vertex_group: StringProperty(name="Vertex Group", update=update_geo_node_instance_values, description="Name of the vertex group to use as a density mask")
    density_mask_socket_identifier: StringProperty()

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
class PAINTERLY_OT_RefreshPrimaryMaterial(Operator):
    bl_idname = "painterly.refresh_material"
    bl_label = "Refresh Primary Material"
    bl_description = "Updates the Geometry Node setup to use the primary object's current material"
    bl_options = {'REGISTER', 'UNDO'}

    primary_stroke_index: IntProperty()

    def execute(self, context):
        geo_props = context.scene.geo_node_properties
        if self.primary_stroke_index >= len(geo_props.primary_strokes):
            return {'CANCELLED'}
            
        primary_stroke = geo_props.primary_strokes[self.primary_stroke_index]
        obj = primary_stroke.obj
        if not _obj_alive(obj):
            return {'CANCELLED'}

        mod = get_geo_node_modifier(obj)
        if not mod or not mod.node_group:
            return {'CANCELLED'}
        
        set_mat_node = mod.node_group.nodes.get("Painterly_Set_Material")
        if set_mat_node:
            set_mat_node.inputs["Material"].default_value = obj.active_material
            self.report({'INFO'}, f"Material updated for '{obj.name}'.")
        
        return {'FINISHED'}


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
        
        if not _obj_alive(primary_obj):
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
            if not _obj_alive(secondary_obj): continue
            if primary_obj == secondary_obj: continue
            if any(ps.obj == secondary_obj for ps in geo_props.primary_strokes): continue
            if any(ss.obj == secondary_obj for ss in primary_stroke_target.secondary_strokes): continue
            
            ss_prop = primary_stroke_target.secondary_strokes.add()
            ss_prop.name = secondary_obj.name
            ss_prop.obj = secondary_obj

            secondary_name = _secondary_safe_name(secondary_obj.name)
            y_pos = -550 * (len(primary_stroke_target.secondary_strokes))
            
            n_dist = nodes.new("GeometryNodeDistributePointsOnFaces")
            n_dist.name = f"Distribute_{secondary_name}"; n_dist.location = (-50, y_pos)
            n_dist.distribute_method = 'POISSON'
            
            if "Density Max" in n_dist.inputs:
                n_dist.inputs["Density Max"].default_value = ss_prop.density
            elif "Density" in n_dist.inputs:
                n_dist.inputs["Density"].default_value = ss_prop.density

            socket_name = f"Density Mask {secondary_name}"
            socket_item = ng.interface.new_socket(name=socket_name, in_out="INPUT", socket_type='NodeSocketFloat')
            socket_item.subtype = 'FACTOR'
            socket_item.default_value = 1.0
            socket_item.min_value = 0.0
            socket_item.max_value = 1.0
            socket_item.description = "Vertex group mask for instance density"
            ss_prop.density_mask_socket_identifier = socket_item.identifier

            mask_socket = next((s for s in n_in.outputs if s.identifier == ss_prop.density_mask_socket_identifier), None)
            if mask_socket:
                target_density_factor = n_dist.inputs.get("Density Factor") or n_dist.inputs.get("Density")
                if target_density_factor:
                    links.new(mask_socket, target_density_factor)

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
            try:
                n_align_rot = nodes.new("GeometryNodeVectorToRotation")
            except RuntimeError:
                try:
                    n_align_rot = nodes.new("FunctionNodeAlignRotationToVector")
                except RuntimeError:
                    n_align_rot = None

            if n_align_rot:
                n_align_rot.name = f"AlignRotation_{secondary_name}"
                n_align_rot.location = (450, y_pos - 350)
                ss_prop.align_rotation_available = True
            else:
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
                
                links.new(n_rand_rot.outputs["Value"], n_switch.inputs['False'])
                links.new(n_align_rot.outputs['Rotation'], n_switch.inputs['True'])
                links.new(n_dist.outputs['Normal'], n_align_rot.inputs['Vector'])
                links.new(n_switch.outputs['Output'], n_instance.inputs['Rotation'])
            else:
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

        for ss in primary_to_remove.secondary_strokes:
            if _obj_alive(ss.obj):
                ss.obj.hide_set(False)
                ss.obj.hide_render = False

        if _obj_alive(obj):
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

        if not _obj_alive(primary_obj):
            # Primary is gone, just remove the property
            primary_stroke.secondary_strokes.remove(self.secondary_stroke_index)
            return {'CANCELLED'}

        secondary_name_stored = secondary_stroke.name # Store before potential removal
        
        mod = get_geo_node_modifier(primary_obj)
        if mod and mod.node_group:
            ng = mod.node_group
            safe_secondary_name = _secondary_safe_name(secondary_name_stored)
            
            nodes_to_remove = [n for n in ng.nodes if n.name.endswith(f"_{safe_secondary_name}")]
            for node in nodes_to_remove:
                ng.nodes.remove(node)
            
            if secondary_stroke.density_mask_socket_identifier:
                socket_to_remove = next((item for item in ng.interface.items_tree if item.identifier == secondary_stroke.density_mask_socket_identifier), None)
                if socket_to_remove:
                    ng.interface.remove(socket_to_remove)

        if _obj_alive(secondary_obj):
            secondary_obj.hide_set(False)
            secondary_obj.hide_render = False
        
        primary_stroke.secondary_strokes.remove(self.secondary_stroke_index)

        self.report({'INFO'}, f"Removed instance '{secondary_name_stored}' from '{primary_obj.name}'.")
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
    for nd in list(node_tree.nodes):
        if nd.name.startswith("PainterlyMagic") or nd.name.startswith("PainterlyVoronoi") or nd.name.startswith("PainterlyNoise"):
            node_tree.nodes.remove(nd)
    if props.effect_type == EFFECT_NONE:
        return
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
    node_tree.links.new(effect_node.inputs["Vector"], mapping_node.outputs["Vector"])
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
    global pending_inactive_ramp_refs
    if pending_inactive_ramp_refs:
        mat_name, node_name = pending_inactive_ramp_refs.pop(0)
        mat = bpy.data.materials.get(mat_name)
        if mat and mat.node_tree:
            ramp_node = mat.node_tree.nodes.get(node_name)
            if ramp_node:
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

def update_displacement_values(self, context):
    obj = context.active_object
    if not obj or not obj.active_material or not obj.active_material.node_tree:
        return
    
    mat_tree = obj.active_material.node_tree
    for node in mat_tree.nodes:
        if node.type == 'DISPLACEMENT':
            node.inputs["Height"].default_value = self.displacement_height
            node.inputs["Midlevel"].default_value = self.displacement_midlevel
            node.inputs["Scale"].default_value = self.displacement_scale


def update_normal_map_strength(self, context):
    obj = context.active_object
    if not obj or not obj.active_material or not obj.active_material.node_tree:
        return

    mat_tree = obj.active_material.node_tree
    for node in mat_tree.nodes:
        if node.type == 'NORMAL_MAP':
            node.inputs['Strength'].default_value = self.normal_map_strength


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
            
            # Move the modifier to the top of the stack
            while obj.modifiers.find(mod.name) > 0:
                bpy.ops.object.modifier_move_up(modifier=mod.name)

            self.report({'INFO'}, "Wave modifier added and moved to top.")
        return {'FINISHED'}

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
                            
                            fcurve.driver.expression = f"int(((frame - 1) / max(step, 1))) % max(fc, 1) + 1 == {index}"
                            
                            driver = fcurve.driver
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
            
            links_to_remove = []
            link_found = False
            for link in node_tree.links:
                if link.to_node == node and link.to_socket == alpha_socket:
                    links_to_remove.append(link)
                    link_found = True

            if props.use_alpha_channel:
                if not link_found and img_node:
                    node_tree.links.new(img_node.outputs["Alpha"], alpha_socket)
            else:
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

    global_tilt: FloatProperty(
        name="Global Tilt",
        default=0.0,
        min=-3.14159,
        max=3.14159,
        update=update_global_tilt
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
            bpy.ops.object.start_maintaining_tilt('INVOKE_DEFAULT')
        else:
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
        name="Size",
        default=0.1,
        min=0.0,
        max=10.0,
        update=lambda s, c: update_extrusion(c)
    )
    extrusion_locked: FloatProperty(
        name="Size (Locked)",
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
        min=-10.0,
        max=10.0,
        update=update_displacement_values
    )
    displacement_midlevel: FloatProperty(
        name="Midlevel",
        default=0.0,
        min=0.0,
        max=1.0,
        update=update_displacement_values
    )
    displacement_scale: FloatProperty(
        name="Scale",
        default=0.0,
        min=0.0,
        max=10.0,
        update=update_displacement_values
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
        max=5.0,
        update=update_normal_map_strength
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

class PresetSelectionItem(PropertyGroup):
    name: StringProperty()
    path: StringProperty()
    selected: BoolProperty(name="", default=False)

def update_include_stroke_pen_alphas(self, context):
    """Callback to refresh the preset list when the option is toggled."""
    sync_combined_preset_list(context)

class PainterlyProperties(PropertyGroup):
    stroke_length: IntProperty(name="Stroke Length", default=1200, min=60, max=6000)
    stroke_width: FloatProperty(name="Stroke Width", default=90.0, min=30.0, max=300.0)
    random_seed: IntProperty(name="Random Seed", default=42, min=1)
    randomness_intensity: FloatProperty(name="Stroke Randomness", default=0.7, min=0.0, max=1.0)
    stroke_opacity: FloatProperty(name="Stroke Opacity", default=1.0, min=0.1, max=1.0)
    randomize_stroke_length: BoolProperty(name="Randomize Stroke Length", default=False)
    stroke_length_min: IntProperty(name="Min Stroke Length", default=300, min=60, max=6000)
    
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
    resolution: EnumProperty(
        name="Resolution",
        description="Resolution of the baked image",
        items=[
            ('512', "512", "512x512"),
            ('1024', "1024", "1024x1024"),
            ('2048', "2048", "2048x2048"),
            ('4096', "4096", "4096x4096"),
            ('8192', "8192", "8192x8192"),
        ],
        default='1024'
    )
    process_all_materials: BoolProperty(
        name="Process All Material Slots",
        description="When enabled, 'Apply Painterly Effect' will process all materials on the object",
        default=False
    )
    preserve_material_color: BoolProperty(
        name="Preserve Material Color",
        description="Reconnect the original material's color after applying the painterly effect",
        default=True
    )
    dynamic_strokes: FloatProperty(
        name="Dynamic Strokes",
        description="Controls how much the normal map influences stroke angle, size, and randomness. 0=uniform, 1=max creativity",
        default=0.2,
        min=0.0,
        max=1.0
    )
    average_stroke_size: FloatProperty(
        name="Average Stroke Size",
        description="Controls the overall average size of the generated strokes",
        default=1.0,
        min=0.01,
        max=10.0
    )
    stroke_density: FloatProperty(
        name="Stroke Density",
        description="Controls the number of strokes generated. Higher values mean more strokes",
        default=1.0,
        min=0.01,
        max=10.0
    )
    show_preset_list: BoolProperty(
        name="List Presets",
        description="Toggle between single preset selection and a list for selecting multiple packs",
        default=False
    )
    include_stroke_pen_alphas: BoolProperty(
        name="Include Stroke Pen Alphas",
        description="Use brushes from the Stroke Pen mode in the Painterly Texture generator",
        default=False,
        update=update_include_stroke_pen_alphas
    )
    enable_color_pass: BoolProperty(
        name="Enable Color Pass",
        description="Process the material's Base Color texture with painterly strokes in addition to the normal map",
        default=False
    )
    only_color_pass: BoolProperty(
        name="Only Color Pass",
        description="When enabled, only the color pass will be processed, skipping the normal pass",
        default=False
    )
    preset_selections: CollectionProperty(type=PresetSelectionItem)

class PAINTERLY_OT_SelectAllPresets(Operator):
    bl_idname = "painterly.select_all_presets"
    bl_label = "Select/Deselect All Presets"
    select_all: BoolProperty()
    def execute(self, context):
        stylized_props = context.scene.stylized_painterly_properties
        for item in stylized_props.preset_selections:
            item.selected = self.select_all
        return {'FINISHED'}

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

def scheduled_update_check():
    """Wrapper function for the timer to prevent return value errors."""
    bpy.ops.painterly.check_for_updates('INVOKE_DEFAULT')
    return None

@persistent
def painterly_depsgraph_update_post(scene, depsgraph):
    try:
        if not scene or not scene.world:
            return
        geo_props = scene.geo_node_properties
    except (ReferenceError, AttributeError):
        return
        
    # --- START: Auto-cleanup for invalid secondary strokes ---
    for ps_index, ps in enumerate(getattr(geo_props, "primary_strokes", [])):
        if not _obj_alive(ps.obj): # Skip if the primary itself is invalid
            continue

        indices_to_remove = [i for i, ss in enumerate(ps.secondary_strokes) if not _obj_alive(ss.obj)]

        if indices_to_remove:
            mod = get_geo_node_modifier(ps.obj)
            ng = mod.node_group if (mod and mod.node_group) else None

            # Remove in reverse to not mess up indices
            for i in sorted(indices_to_remove, reverse=True):
                secondary_stroke = ps.secondary_strokes[i]
                secondary_name_stored = secondary_stroke.name
                socket_identifier = secondary_stroke.density_mask_socket_identifier

                if ng:
                    safe_secondary_name = _secondary_safe_name(secondary_name_stored)

                    # Remove nodes
                    nodes_to_remove = [n for n in ng.nodes if n.name.endswith(f"_{safe_secondary_name}")]
                    for node in nodes_to_remove:
                        ng.nodes.remove(node)

                    # Remove interface socket
                    if socket_identifier:
                        socket_to_remove = next((item for item in ng.interface.items_tree if item.identifier == socket_identifier), None)
                        if socket_to_remove:
                            ng.interface.remove(socket_to_remove)
                
                # Finally remove the property group
                ps.secondary_strokes.remove(i)
                print(f"[Painterly] Auto-removed invalid instance '{secondary_name_stored}' from '{ps.obj.name}'.")
    # --- END: Auto-cleanup ---
        
    for ps in getattr(geo_props, "primary_strokes", []):
        obj = getattr(ps, "obj", None)
        if not _obj_alive(obj):
            continue
        mod = get_geo_node_modifier(obj)
        if not (mod and mod.node_group and obj.active_material):
            continue
        set_mat = mod.node_group.nodes.get("Painterly_Set_Material")
        if set_mat:
            if set_mat.inputs["Material"].default_value != obj.active_material:
                set_mat.inputs["Material"].default_value = obj.active_material
                _force_gn_refresh(obj)

@persistent
def painterly_load_post_handler(dummy):
    if painterly_frame_change_post not in bpy.app.handlers.frame_change_post:
        bpy.app.handlers.frame_change_post.append(painterly_frame_change_post)
    if painterly_depsgraph_update_post not in bpy.app.handlers.depsgraph_update_post:
        bpy.app.handlers.depsgraph_update_post.append(painterly_depsgraph_update_post)
        
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
        props.folder_configured = bool(props.base_path)
        
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
            bpy.app.timers.register(scheduled_update_check, first_interval=1)
        
        refresh_all_painterly_strokes(bpy.context)

        for obj in bpy.context.scene.objects:
            if obj.type == 'CURVE':
                data = obj.data
                if hasattr(data, "get") and "painterly_stroke_path" in data and "painterly_stroke_path" not in obj:
                    obj["painterly_stroke_path"] = data["painterly_stroke_path"]

        # Run the driver repair function to fix old files
        _repair_painterly_drivers_after_update(scn)

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
            
            bpy.ops.curve.primitive_bezier_curve_add(enter_editmode=False, align='WORLD', location=(0,0,0))
            new_curve = context.active_object
            new_curve.name = base_obj_name
            curve_data = new_curve.data
            curve_data.name = base_obj_name + "_Curve"

            while curve_data.splines:
                curve_data.splines.remove(curve_data.splines[0])
            
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
                mix_prev.name = "Mix Shader_1"
                mix_prev.location = (-400, 400)
                links.new(transp.outputs["BSDF"], mix_prev.inputs[1])
                links.new(base_nodes[0].outputs["BSDF"], mix_prev.inputs[2])
                drv = mix_prev.inputs[0].driver_add("default_value").driver
                
                drv.expression = "int(((frame - 1) / max(step, 1))) % max(fc, 1) + 1 == 1"
                
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
                    mix_node.name = f"Mix Shader_{i+1}"
                    mix_node.location = (-400, 400 - i * 200)
                    links.new(mix_nodes[-1].outputs["Shader"], mix_node.inputs[1])
                    links.new(base_nodes[i].outputs["BSDF"], mix_node.inputs[2])
                    drv = mix_node.inputs[0].driver_add("default_value").driver

                    drv.expression = f"int(((frame - 1) / max(step, 1))) % max(fc, 1) + 1 == {i+1}"
                    
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
                normal_map_node.name = "Normal Map_1"
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
            if not obj.active_material:
                obj.data.materials.append(mat)
            obj.active_material = mat
            mat.use_nodes = True
            nds = mat.node_tree.nodes
            lnks = mat.node_tree.links
            bsdf = next((n for n in nds if n.type == 'BSDF_PRINCIPLED'), None)
            if not bsdf:
                bsdf = nds.new("ShaderNodeBsdfPrincipled")

            tex_image = nds.new('ShaderNodeTexImage')
            image_name = f"{obj.name}_NORM_MAP"
            
            res = int(stylized_props.resolution)

            if image_name in bpy.data.images:
                image = bpy.data.images[image_name]
                image.scale(res, res)
            else:
                image = bpy.data.images.new(name=image_name, width=res, height=res, alpha=True)
                
            tex_image.image = image
            
            for link in bsdf.inputs['Base Color'].links:
                lnks.remove(link)
            lnks.new(bsdf.inputs['Base Color'], tex_image.outputs['Color'])
            
            normal_map_node = nds.new('ShaderNodeNormalMap')
            normal_map_node.space = 'OBJECT'
            normal_map_node.inputs['Strength'].default_value = 0.4
            
            for link in normal_map_node.inputs['Color'].links:
                lnks.remove(link)
            lnks.new(normal_map_node.inputs['Color'], tex_image.outputs['Color'])
            
            for link in bsdf.inputs['Normal'].links:
                lnks.remove(link)
            lnks.new(bsdf.inputs['Normal'], normal_map_node.outputs['Normal'])

            scn = bpy.context.scene
            scn.render.bake.use_selected_to_active = False
            scn.render.bake.margin = 3
            scn.render.bake.use_clear = True
            scn.cycles.bake_type = 'NORMAL'
            scn.render.bake.normal_space = 'OBJECT'
            mat.node_tree.nodes.active = tex_image
            
            self.report({'INFO'}, f"Baking to {res}x{res} image. This may take a moment...")
            bpy.ops.object.bake(type='NORMAL')
            
            self.report({'INFO'}, "Baking completed successfully")
            stylized_props.image = image
            image.pack()
            return {'FINISHED'}
        except Exception as e:
            self.report({'ERROR'}, f"Baking failed: {e}")
            return {'CANCELLED'}

class PAINTERLY_OT_CancelEffect(Operator):
    bl_idname = "painterly.cancel_effect"
    bl_label = "Cancel Painterly Process"
    bl_description = "Stops the ongoing Painterly texture generation"

    def execute(self, context):
        context.window_manager.painterly_cancel_requested = True
        self.report({'INFO'}, "Cancellation requested.")
        return {'FINISHED'}

class PainterlyEffectOperator(Operator):
    bl_idname = "texture.apply_painterly_effect"
    bl_label = "Apply Painterly Effect"
    bl_options = {'REGISTER', 'UNDO'}

    _timer = None
    _executor = None
    _futures = None
    _stroke_tasks = None
    _loaded_brushes = None
    
    # Cache for resized brushes
    _brush_cache = {}

    materials_to_process = []
    current_material_index = 0
    current_pass: StringProperty(default='NORMAL')
    
    _original_color_connections = {}
    _source_color_images = {}
    _source_normal_images = {}

    def _cleanup(self, context, cancelled=False):
        """Safely clean up modal resources."""
        if self._timer:
            context.window_manager.event_timer_remove(self._timer)
            self._timer = None
        if self._executor:
            self._executor.shutdown(wait=False, cancel_futures=True)
            self._executor = None
        self._futures = None
        self._brush_cache.clear() # Clear cache on cleanup
        
        context.window_manager.progress_end()
        if cancelled:
            self.report({'INFO'}, "Painterly process cancelled.")
        else:
            self.report({'INFO'}, "Painterly process finished.")
        
        context.window_manager.painterly_is_processing = False

    def modal(self, context, event):
        if context.window_manager.painterly_cancel_requested:
            self._cleanup(context, cancelled=True)
            return {'CANCELLED'}

        if event.type == 'ESC':
            self._cleanup(context, cancelled=True)
            return {'CANCELLED'}

        if event.type == 'TIMER':
            if not self._executor or not self._futures:
                self._cleanup(context)
                return {'FINISHED'}
            
            done_count = sum(1 for f in self._futures if f.done())
            
            current_mat_name = self.materials_to_process[self.current_material_index].name
            progress_msg = f"Painterly: Processing '{current_mat_name}' - {self.current_pass} Pass ({done_count}/{len(self._futures)})"
            context.workspace.status_text_set(progress_msg)
            context.window_manager.painterly_progress_text = f"{self.current_pass} ({done_count}/{len(self._futures)})"
            
            if done_count == len(self._futures):
                mat_to_process = self.materials_to_process[self.current_material_index]
                self.finalize_tile(context, mat_to_process)
                self._advance_state(context)
                if self.current_material_index >= len(self.materials_to_process):
                    self._cleanup(context)
                    return {'FINISHED'}
                else:
                    self.setup_for_next_job(context)

        return {'PASS_THROUGH'}

    def _advance_state(self, context):
        stylized_props = context.scene.stylized_painterly_properties
        current_mat = self.materials_to_process[self.current_material_index]
        
        if self.current_pass == 'COLOR' and not stylized_props.only_color_pass:
            self.current_pass = 'NORMAL'
        else:
            self.finalize_node_setup(context, current_mat)
            self.current_material_index += 1
            if self.current_material_index < len(self.materials_to_process):
                self.current_pass = 'COLOR' if stylized_props.enable_color_pass else 'NORMAL'
    
    def invoke(self, context, event):
        if not check_pillow():
            self.report({'ERROR'}, "Pillow library not installed. Please install it in Add-on Preferences.")
            return {'CANCELLED'}
        
        context.window_manager.painterly_is_processing = True
        context.window_manager.painterly_cancel_requested = False
            
        scene = context.scene
        stylized_props = scene.stylized_painterly_properties
        folder_props = scene.painterly_folder_properties
        
        obj_ref = context.active_object
        if not obj_ref:
            self.report({'ERROR'}, "No active object selected.")
            context.window_manager.painterly_is_processing = False
            return {'CANCELLED'}
            
        self.materials_to_process.clear()
        self._original_color_connections.clear()
        self._source_color_images.clear()
        self._source_normal_images.clear()
        
        if not obj_ref.material_slots:
            self.report({'INFO'}, "Object has no materials. Creating a new one.")
            new_mat = bpy.data.materials.new(name=f"{obj_ref.name}_PainterlyMat")
            new_mat.use_nodes = True
            obj_ref.data.materials.append(new_mat)
        
        if stylized_props.process_all_materials:
            self.materials_to_process = [slot.material for slot in obj_ref.material_slots if slot.material]
        else:
            if obj_ref.active_material:
                self.materials_to_process.append(obj_ref.active_material)

        if not self.materials_to_process:
            self.report({'ERROR'}, "No materials to process. Assign a material or use 'Process All'.")
            context.window_manager.painterly_is_processing = False
            return {'CANCELLED'}
        
        for mat in self.materials_to_process:
            if not mat.use_nodes: mat.use_nodes = True
            if mat.node_tree is None: continue

            bsdf = next((n for n in mat.node_tree.nodes if n.type == 'BSDF_PRINCIPLED'), None)
            if bsdf:
                if bsdf.inputs['Base Color'].is_linked:
                    from_node = bsdf.inputs['Base Color'].links[0].from_node
                    if from_node.type == 'TEX_IMAGE' and from_node.image:
                        self._source_color_images[mat.name] = from_node.image
                
                if bsdf.inputs['Normal'].is_linked:
                    from_node = bsdf.inputs['Normal'].links[0].from_node
                    if from_node.type == 'NORMAL_MAP' and from_node.inputs['Color'].is_linked:
                        from_node_2 = from_node.inputs['Color'].links[0].from_node
                        if from_node_2.type == 'TEX_IMAGE' and from_node_2.image:
                            self._source_normal_images[mat.name] = from_node_2.image

            if stylized_props.enable_color_pass and mat.name not in self._source_color_images:
                 self.report({'WARNING'}, f"Material '{mat.name}' has no Image Texture for Color Pass. Skipping Color Pass.")
            
            if not stylized_props.only_color_pass and mat.name not in self._source_normal_images:
                self.report({'INFO'}, f"Material '{mat.name}' has no source normal map. Auto-baking...")
                context.view_layer.objects.active = obj_ref
                obj_ref.active_material_index = obj_ref.material_slots.find(mat.name)
                bpy.ops.texture.auto_bake('EXEC_DEFAULT')
                self._source_normal_images[mat.name] = bpy.data.images.get(f"{obj_ref.name}_NORM_MAP")

        self._loaded_brushes = []
        selected_presets = []
        if stylized_props.show_preset_list:
            selected_presets = [p for p in stylized_props.preset_selections if p.selected]
        else:
            if stylized_props.include_stroke_pen_alphas:
                if folder_props.stroke_folders:
                    selected_presets = [folder_props.stroke_folders[folder_props.current_stroke_index]]
            else:
                if folder_props.preset_folders:
                    selected_presets = [folder_props.preset_folders[folder_props.current_preset_index]]

        if not selected_presets:
            self.report({'ERROR'}, "No preset folders selected. Please select at least one preset.")
            context.window_manager.painterly_is_processing = False
            return {'CANCELLED'}

        for preset in selected_presets:
            if os.path.isdir(preset.path):
                try:
                    from PIL import Image
                    for dirpath, _, filenames in os.walk(preset.path):
                        for f in filenames:
                            if f.lower().endswith('.png'):
                                full_path = os.path.join(dirpath, f)
                                self._loaded_brushes.append(Image.open(full_path).convert("RGBA"))
                except Exception as e:
                    self.report({'ERROR'}, f"Failed to load brushes from '{preset.name}': {e}")
                    context.window_manager.painterly_is_processing = False
                    return {'CANCELLED'}

        if not self._loaded_brushes:
            self.report({'ERROR'}, "Selected preset folders contain no valid .png brushes.")
            context.window_manager.painterly_is_processing = False
            return {'CANCELLED'}

        self.current_material_index = 0
        self.current_pass = 'COLOR' if stylized_props.enable_color_pass else 'NORMAL'
        
        self.setup_for_next_job(context)

        context.window_manager.progress_begin(0, 100)
        self._timer = context.window_manager.event_timer_add(0.5, window=context.window)
        context.window_manager.modal_handler_add(self)
        self.report({'INFO'}, f"Starting Painterly process on {len(self.materials_to_process)} material(s)...")
        return {'RUNNING_MODAL'}

    def setup_for_next_job(self, context):
        from PIL import Image
        stylized_props = context.scene.stylized_painterly_properties
        current_mat = self.materials_to_process[self.current_material_index]

        source_image = None
        color_pil = None
        normal_pil = None
        
        source_normal_image = self._source_normal_images.get(current_mat.name)
        if source_normal_image:
            try:
                norm_w, norm_h = source_normal_image.size
                norm_pixels = np.array(source_normal_image.pixels[:]).reshape(norm_h, norm_w, 4) * 255
                normal_pil = Image.fromarray(norm_pixels.astype(np.uint8), 'RGBA')
            except (ValueError, IndexError) as e:
                self.report({'ERROR'}, f"Could not process normal map for '{current_mat.name}': {e}. Check dimensions.")
                self._advance_state(context)
                if self.current_material_index < len(self.materials_to_process): self.setup_for_next_job(context)
                return
        
        if self.current_pass == 'COLOR':
            source_image = self._source_color_images.get(current_mat.name)
            if not source_image or not normal_pil:
                self._advance_state(context)
                if self.current_material_index < len(self.materials_to_process): self.setup_for_next_job(context)
                return
            
            w, h = source_image.size
            pixels = np.array(source_image.pixels[:]).reshape(h, w, 4) * 255
            color_pil = Image.fromarray(pixels.astype(np.uint8), 'RGBA')
            
            if (w,h) != normal_pil.size:
                self.report({'WARNING'}, f"Color and Normal map dimensions differ for '{current_mat.name}'. Resizing normal map for this pass.")
                normal_pil = normal_pil.resize((w,h), Image.Resampling.LANCZOS)
        else:
            source_image = source_normal_image

        if not source_image:
             self._advance_state(context)
             if self.current_material_index < len(self.materials_to_process): self.setup_for_next_job(context)
             return
        
        self._stroke_tasks = self.generate_stroke_tasks(normal_pil, color_pil, stylized_props, context, current_mat.name)
        
        if not self._stroke_tasks:
            self._futures = []
            self._advance_state(context)
            if self.current_material_index < len(self.materials_to_process): self.setup_for_next_job(context)
            return

        self._executor = concurrent.futures.ThreadPoolExecutor()
        self._futures = [
            self._executor.submit(
                self.apply_stroke_thread,
                task['brush'], task['pos'], task['angle'], task['length'],
                task['width'], task['opacity'], task['color'], self._brush_cache
            ) for task in self._stroke_tasks
        ]

    def finalize_tile(self, context, material):
        from PIL import Image
        
        w,h = (0,0)
        source_img = None
        if self.current_pass == 'COLOR':
            source_img = self._source_color_images.get(material.name)
        else:
            source_img = self._source_normal_images.get(material.name)
        
        if not source_img: return
        w, h = source_img.size

        painterly_img = Image.new("RGBA", (w, h), (0, 0, 0, 0))

        for future in self._futures:
            if context.window_manager.painterly_cancel_requested: break
            try:
                stroke_img, position = future.result()
                if stroke_img:
                    painterly_img.paste(stroke_img, position, mask=stroke_img)
            except Exception as e:
                print(f"A stroke failed to apply: {e}")
        
        pass_name = "COLOR" if self.current_pass == "COLOR" else "NORMAL"
        paint_name = f"{material.name}_PAINTERLY_{pass_name}"
        
        if paint_name in bpy.data.images:
            blender_res = bpy.data.images[paint_name]
            if blender_res.size[0] != w or blender_res.size[1] != h:
                blender_res.scale(w,h)
        else:
            blender_res = bpy.data.images.new(paint_name, width=w, height=h, alpha=True)

        if self.current_pass == "COLOR":
            blender_res.alpha_mode = 'NONE'

        pixels_flat = (np.array(painterly_img).flatten() / 255.0).astype(np.float32)
        blender_res.pixels.foreach_set(pixels_flat)
        blender_res.pack()

    def finalize_node_setup(self, context, material):
        stylized_props = context.scene.stylized_painterly_properties
        stroke_props = context.scene.stroke_brush_properties

        nds = material.node_tree.nodes
        lnks = material.node_tree.links

        for node in list(nds):
            if node.name.startswith("Painterly_"):
                nds.remove(node)

        bsdf = next((n for n in nds if n.type == 'BSDF_PRINCIPLED'), None)
        if not bsdf: return 

        normal_tex_name = f"{material.name}_PAINTERLY_NORMAL"
        if normal_tex_name in bpy.data.images:
            normal_tex_img = nds.new('ShaderNodeTexImage')
            normal_tex_img.name = "Painterly_Normal_Texture"
            normal_tex_img.image = bpy.data.images[normal_tex_name]
            normal_tex_img.image.colorspace_settings.name = 'Non-Color'
            normal_tex_img.location = (bsdf.location.x - 500, bsdf.location.y - 200)

            normal_map_node = nds.new('ShaderNodeNormalMap')
            normal_map_node.name = "Painterly_Normal_Map"
            normal_map_node.space = 'OBJECT'
            normal_map_node.inputs['Strength'].default_value = stroke_props.normal_map_strength
            normal_map_node.location = (bsdf.location.x - 250, bsdf.location.y - 200)
            
            disp_node = nds.new("ShaderNodeDisplacement")
            disp_node.name = "Painterly_Displacement"
            disp_node.location = (bsdf.location.x - 250, bsdf.location.y - 400)
            disp_node.inputs["Height"].default_value = stroke_props.displacement_height
            disp_node.inputs["Midlevel"].default_value = stroke_props.displacement_midlevel
            disp_node.inputs["Scale"].default_value = stroke_props.displacement_scale

            lnks.new(normal_tex_img.outputs['Color'], normal_map_node.inputs['Color'])
            lnks.new(normal_map_node.outputs['Normal'], bsdf.inputs['Normal'])

            mat_out = next((n for n in nds if n.type == 'OUTPUT_MATERIAL'), None)
            if mat_out:
                lnks.new(normal_map_node.outputs['Normal'], disp_node.inputs['Normal'])
                lnks.new(disp_node.outputs['Displacement'], mat_out.inputs['Displacement'])

        color_tex_name = f"{material.name}_PAINTERLY_COLOR"
        if color_tex_name in bpy.data.images:
            color_tex_img = nds.new('ShaderNodeTexImage')
            color_tex_img.name = "Painterly_Color_Texture"
            color_tex_img.image = bpy.data.images[color_tex_name]
            color_tex_img.image.colorspace_settings.name = 'sRGB'
            color_tex_img.location = (bsdf.location.x - 500, bsdf.location.y)
            lnks.new(color_tex_img.outputs['Color'], bsdf.inputs['Base Color'])
        elif stylized_props.preserve_material_color:
             original_socket = self._original_color_connections.get(material.name)
             if original_socket:
                 lnks.new(original_socket, bsdf.inputs['Base Color'])
        else:
            if normal_tex_name in bpy.data.images:
                lnks.new(nds["Painterly_Normal_Texture"].outputs['Color'], bsdf.inputs['Base Color'])


    def generate_stroke_tasks(self, normal_pil, color_pil, props, context, material_name):
        from PIL import Image, ImageDraw, ImageFilter
        import math
        import numpy

        tasks = []
        random.seed(props.random_seed)
        w, h = normal_pil.size

        if w == 0 or h == 0:
            return []

        try:
            alpha = normal_pil.getchannel('A')
            mask = Image.new('L', (w, h), 0)
            mask.paste(alpha)
        except ValueError:
            mask = Image.new('L', (w, h), 255)

        gray_pil = normal_pil.convert('L')
        edge_map_img = gray_pil.filter(ImageFilter.FIND_EDGES)
        edge_data = np.array(edge_map_img)

        factor = 500.0 / 9.0
        num_strokes = int(props.randomness_intensity * w * h / factor * props.stroke_density)

        for _ in range(num_strokes):
            if context.window_manager.painterly_cancel_requested:
                break

            x = random.randint(0, w - 1)
            y = random.randint(0, h - 1)

            if mask.getpixel((x, y)) < 10:
                continue

            px_normal = normal_pil.getpixel((x, y))
            if px_normal[0] < 10 and px_normal[1] < 10 and px_normal[2] < 10:
                continue

            dynamic_factor = props.dynamic_strokes
            
            x_comp = (px_normal[0] / 255.0) * 2.0 - 1.0
            y_comp = (px_normal[1] / 255.0) * 2.0 - 1.0
            base_angle_rad = math.atan2(y_comp, x_comp)
            base_angle_deg = math.degrees(base_angle_rad)
            angle_randomness = (random.random() * 2 - 1) * 90 * dynamic_factor
            final_angle = base_angle_deg + angle_randomness

            final_width = 0
            final_length = 0

            if random.random() < (0.15 * dynamic_factor):
                size_boost = 1.5 + (2.5 * dynamic_factor * random.random())
                elongation_boost = 1.5 + (2.0 * dynamic_factor * random.random())
                final_width = (props.stroke_width * props.average_stroke_size) * size_boost
                final_length = final_width * elongation_boost
            else:
                edge_strength = edge_data[y, x] / 255.0
                open_space_factor = 1.0 - edge_strength
                base_width = props.stroke_width * props.average_stroke_size
                edge_scale_modifier = (open_space_factor * 0.9) + 0.1
                size_modifier = 1.0 - (1.0 - edge_scale_modifier) * dynamic_factor
                final_width = base_width * size_modifier
                elongation_factor = 1.0 + (open_space_factor * 2.0 * dynamic_factor)
                final_length = final_width * elongation_factor
            
            final_color = (0,0,0,0)
            if color_pil:
                px_color = color_pil.getpixel((x, y))
                final_color = (
                    px_color[0], px_color[1], px_color[2], 
                    int(props.stroke_opacity * 255)
                )
            else:
                c_r = px_normal[0] + random.randint(-20, 20)
                c_g = px_normal[1] + random.randint(-20, 20)
                c_b = px_normal[2] + random.randint(-20, 20)
                final_color = (
                    int(max(0, min(255, c_r))),
                    int(max(0, min(255, c_g))),
                    int(max(0, min(255, c_b))),
                    int(props.stroke_opacity * 255)
                )

            tasks.append({
                'brush': random.choice(self._loaded_brushes),
                'pos': (x, y),
                'angle': final_angle,
                'length': final_length,
                'width': final_width,
                'opacity': props.stroke_opacity,
                'color': final_color,
            })
        
        print(f"Painterly: [{self.current_pass} PASS] Generated {len(tasks)} strokes for material '{material_name}'.")
        return tasks
    
    @staticmethod
    def apply_stroke_thread(brush_stroke, pos, angle, length, width, opacity, color, brush_cache):
        from PIL import Image
        import numpy as np
        try:
            x, y = pos
            size_x = max(1, int(width))
            size_y = max(1, int(length))
            
            # Use a tuple of (original_brush_id, size_x, size_y) as the cache key
            cache_key = (id(brush_stroke), size_x, size_y)
            
            if cache_key in brush_cache:
                brush_resized = brush_cache[cache_key]
            else:
                brush_resized = brush_stroke.resize((size_x, size_y), Image.Resampling.LANCZOS)
                brush_cache[cache_key] = brush_resized

            brush_rotated = brush_resized.rotate(angle, expand=True, resample=Image.Resampling.BICUBIC)

            # Optimization with NumPy
            brush_arr = np.array(brush_rotated)
            
            # Create an array for the color
            color_arr = np.array(color, dtype=np.uint8)
            
            # Use the alpha channel of the brush to blend the color
            alpha = brush_arr[:, :, 3] / 255.0
            
            # Create a colored stroke array
            colored_stroke_arr = np.zeros_like(brush_arr)
            colored_stroke_arr[:, :, :3] = color_arr[:3]
            colored_stroke_arr[:, :, 3] = (alpha * color_arr[3]).astype(np.uint8)
            
            colored_stroke = Image.fromarray(colored_stroke_arr, 'RGBA')

            offset_x = x - brush_rotated.width // 2
            offset_y = y - brush_rotated.height // 2
            return (colored_stroke, (offset_x, offset_y))
        except Exception as e:
            print(f"Error applying stroke in thread: {e}")
            return (None, None)

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
                        drv.expression = f"1 - (int(((frame - 1) / max(step, 1))) % max(fc, 1) + 1 == {i+1})"
                        
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
    if not _obj_alive(obj):
        return None
    path = obj.get("painterly_stroke_path") or getattr(obj.data, "get", lambda k: None)("painterly_stroke_path")
    if not path:
        return None
        
    for item in folder_props.stroke_folders:
        if os.path.normpath(path).startswith(os.path.normpath(item.path)):
             return item
    return None
    
def get_stroke_colors(obj):
    colors = []
    if not _obj_alive(obj) or not obj.active_material or not obj.active_material.node_tree:
        return colors
        
    mat_nodes = obj.active_material.node_tree.nodes
    ramp_node = mat_nodes.get("StrokeColorRamp_1")
    
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
                    if _obj_alive(active_obj):
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
                            if _obj_alive(ps.obj):
                                self.draw_primary_stroke_box(geo_node_box, ps, i, context)
                else:
                    self.draw_legacy_stroke_pen_ui(context)
            else:
                self.draw_legacy_stroke_pen_ui(context)

        elif addon_props.active_mode == 'PAINTERLY_TEXTURE':
            self.draw_painterly_texture_ui(context)

    def draw_primary_stroke_box(self, layout, ps, index, context):
        """Helper to draw the UI box for a single primary stroke."""
        if not _obj_alive(ps.obj):
            return 
            
        folder_props = context.scene.painterly_folder_properties
        box = layout.box()
        
        header_row = box.row(align=True)
        header_row.alignment = 'LEFT'

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
        
        header_row.label(text=f"{ps.obj.name}", icon='MOD_CURVE')
        
        op_rem_ps = header_row.operator("painterly.remove_primary_stroke", text="", icon='X')
        op_rem_ps.primary_stroke_index = index

        instance_box = box.box()
        row = instance_box.row(align=True)
        row.alignment = 'LEFT'
        row.label(text=f"Instances ({len(ps.secondary_strokes)})", icon='OBJECT_DATA')
        
        if not ps.secondary_strokes:
            instance_box.label(text="   (Empty)", icon='INFO')
        
        for j, ss in enumerate(ps.secondary_strokes):
            if not _obj_alive(ss.obj):
                continue
                
            ss_box = instance_box.box()
            ss_header = ss_box.row(align=True)

            op_vis = ss_header.operator("painterly.toggle_instance_visibility", text="", icon='RESTRICT_VIEW_OFF' if not ss.obj.hide_get() else 'RESTRICT_VIEW_ON', emboss=False)
            op_vis.obj_name = ss.obj.name

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

            op_sel = ss_header.operator("painterly.select_object", text=ss.obj.name, emboss=False)
            op_sel.obj_name = ss.obj.name
            
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
            
            density_mask_box = ss_controls_box.box()
            density_mask_box.label(text="Density Mask", icon='MOD_VERTEX_WEIGHT')

            row_dm = density_mask_box.row()
            row_dm.scale_y = 1.3
            row_dm.prop(ss, "use_density_mask", text="Use Density Mask", icon='STROKE', toggle=True)

            if ps.obj.type == 'MESH':
                if ss.use_density_mask:
                    density_mask_box.prop_search(
                        ss, "density_vertex_group",
                        ps.obj, "vertex_groups",
                        text="Mask"
                    )
            elif ss.use_density_mask:
                density_mask_box.label(text="Primary object must be a Mesh to use a vertex-group mask.", icon='ERROR')

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
        
        # --- MODIFICATION START ---
        # Moved the "Stroke Size" section here.
        extr_box = layout.box()
        extr_box.label(text="Stroke Size")
        if stroke_props.lock_depth_to_extrusion:
            extr_box.prop(stroke_props, "extrusion_locked", slider=True)
        else:
            extr_box.prop(stroke_props, "extrusion", slider=True)
        extr_box.prop(stroke_props, "lock_depth_to_extrusion")
        if not stroke_props.lock_depth_to_extrusion:
            extr_box.prop(stroke_props, "depth", slider=True)
        # --- MODIFICATION END ---
        
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
        stroke_props = context.scene.stroke_brush_properties
        obj = context.active_object
        image_scale = 12

        box = layout.box()
        box.label(text="Brush Preset Selection")
        box.prop(stylized_props, "include_stroke_pen_alphas", toggle=True)

        if stylized_props.include_stroke_pen_alphas:
            cat_box = box.box()
            cat_box.label(text="Category Selection")
            cat_box.prop(folder_props, "selected_stroke_type", text="Main")
            if folder_props.selected_stroke_type != "ALL":
                cat_box.prop(folder_props, "selected_stroke_subtype", text="Subfolder")

        box.prop(stylized_props, "show_preset_list", toggle=True)
        
        if stylized_props.show_preset_list:
            preset_box = box.box()
            row = preset_box.row(align=True)
            row.operator("painterly.select_all_presets", text="All").select_all = True
            row.operator("painterly.select_all_presets", text="None").select_all = False
            scroll_box = preset_box.box()
            for item in stylized_props.preset_selections:
                row = scroll_box.row(align=True)
                row.prop(item, "selected")
                row.label(text=item.name)
        else:
            p_box = box.box()
            row2 = p_box.row(align=True)
            
            nav_folder_type = 'stroke' if stylized_props.include_stroke_pen_alphas else 'preset'

            op_prev = row2.operator("painterly.navigate_folder", text="<", emboss=True)
            op_prev.folder_type = nav_folder_type
            op_prev.direction = 'PREV'

            collection_to_use = folder_props.stroke_folders if stylized_props.include_stroke_pen_alphas else folder_props.preset_folders
            index_to_use = folder_props.current_stroke_index if stylized_props.include_stroke_pen_alphas else folder_props.current_preset_index
            
            if collection_to_use:
                if index_to_use < len(collection_to_use):
                    cpres = collection_to_use[index_to_use]
                    row2.label(text=cpres.name)
                    if cpres.preview_image and cpres.preview_image not in custom_icons:
                        try:
                            custom_icons.load(cpres.preview_image, cpres.preview_filepath, 'IMAGE')
                        except:
                            pass
                    if cpres.preview_image and cpres.preview_image in custom_icons:
                        preview_box = p_box.box()
                        preview_box.template_icon(icon_value=custom_icons[cpres.preview_image].icon_id, scale=image_scale)

            op_next = row2.operator("painterly.navigate_folder", text=">", emboss=True)
            op_next.folder_type = nav_folder_type
            op_next.direction = 'NEXT'
        
        layout.operator("texture.auto_bake")
        layout.separator()
        
        color_pass_box = layout.box()
        color_pass_box.prop(stylized_props, "enable_color_pass", toggle=True)
        row = color_pass_box.row()
        row.prop(stylized_props, "only_color_pass")
        row.enabled = stylized_props.enable_color_pass
        
        settings_box = layout.box()
        settings_box.label(text="Texture Generation Settings")
        
        settings_box.prop(stylized_props, "stroke_density", slider=True)
        settings_box.prop(stylized_props, "average_stroke_size", slider=True)
        settings_box.separator()
        settings_box.prop(stylized_props, "dynamic_strokes", slider=True)
        
        settings_box.separator()
        
        settings_box.prop(stylized_props, "random_seed")
        settings_box.prop(stylized_props, "resolution", text="Resolution")
        settings_box.prop(stroke_props, "normal_map_strength", slider=True)

        disp_box = settings_box.box()
        disp_box.label(text="Displacement")
        disp_box.prop(stroke_props, "displacement_height", text="Height", slider=True)
        disp_box.prop(stroke_props, "displacement_midlevel", text="Midlevel", slider=True)
        disp_box.prop(stroke_props, "displacement_scale", text="Scale", slider=True)
        
        color_box = settings_box.box()
        color_box.label(text="Material & Color")
        color_box.prop(stylized_props, "preserve_material_color")

        if _obj_alive(obj):
            mat_slots_box = settings_box.box()
            mat_slots_box.label(text="Material Slots")
            if obj.material_slots:
                mat_slots_box.prop(stylized_props, "process_all_materials")
                for i, slot in enumerate(obj.material_slots):
                    row = mat_slots_box.row(align=True)
                    icon = 'DOT'
                    if i == obj.active_material_index:
                        icon = 'TRIA_RIGHT'
                    row.label(text=slot.name or "Empty Slot", icon=icon)
            else:
                mat_slots_box.label(text="No material slots on object.")
        else:
            settings_box.label(text="No active object selected.", icon='ERROR')
        
        is_processing = getattr(context.window_manager, 'painterly_is_processing', False)
        
        if not check_pillow():
            layout.operator("painterly.install_dependencies", text="Install Dependencies", icon='IMPORT')
        elif is_processing:
            layout.operator("painterly.cancel_effect", text="CANCEL", icon='CANCEL', depress=True)
            progress_text = getattr(context.window_manager, 'painterly_progress_text', "")
            layout.label(text=f"Processing... {progress_text}")
        else:
            layout.operator("texture.apply_painterly_effect", text="Apply Painterly Effect", icon='PLUS')

        layout.label(text="Processing may take a moment.", icon='INFO')


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
    PresetSelectionItem,
    PainterlyProperties,
    PAINTERLY_OT_SelectAllPresets,
    GeoNodeSecondaryStroke,
    GeoNodePrimaryStroke,
    GeoNodeProperties,
    StrokeBrushProperties,
    PAINTERLY_OT_RefreshPrimaryMaterial,
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
    PAINTERLY_OT_CancelEffect,
    AddDisplacementOperator,
    StrokeBrushPanel,
    RefreshPreviewsOperator,
    PAINTERLY_OT_ToggleWaveModifier,
]


def register():
    global custom_icons
    custom_icons = bpy.utils.previews.new()
    
    bpy.types.WindowManager.painterly_is_processing = BoolProperty(default=False)
    bpy.types.WindowManager.painterly_cancel_requested = BoolProperty(default=False)
    bpy.types.WindowManager.painterly_progress_text = StringProperty(default="")
    
    for cls in classes_to_register:
        bpy.utils.register_class(cls)

    bpy.types.Scene.painterly_folder_properties = PointerProperty(type=PainterlyFolderProperties)
    bpy.types.Scene.addon_properties = PointerProperty(type=AddonProperties)
    bpy.types.Scene.stroke_brush_properties = PointerProperty(type=StrokeBrushProperties)
    bpy.types.Scene.stylized_painterly_properties = PointerProperty(type=PainterlyProperties)
    bpy.types.Scene.geo_node_properties = PointerProperty(type=GeoNodeProperties)

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
    if painterly_depsgraph_update_post not in bpy.app.handlers.depsgraph_update_post:
        bpy.app.handlers.depsgraph_update_post.append(painterly_depsgraph_update_post)

def unregister():
    global custom_icons

    if painterly_depsgraph_update_post in bpy.app.handlers.depsgraph_update_post:
        bpy.app.handlers.depsgraph_update_post.remove(painterly_depsgraph_update_post)
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
        
        if hasattr(bpy.types.WindowManager, 'painterly_is_processing'):
            del bpy.types.WindowManager.painterly_is_processing
        if hasattr(bpy.types.WindowManager, 'painterly_cancel_requested'):
            del bpy.types.WindowManager.painterly_cancel_requested
        if hasattr(bpy.types.WindowManager, 'painterly_progress_text'):
            del bpy.types.WindowManager.painterly_progress_text

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
