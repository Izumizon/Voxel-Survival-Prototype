"""
voxel_survival.py

A complete Minecraft-inspired voxel survival prototype made with Python + Ursina.

Install:
    python -m pip install ursina

Run:
    python voxel_survival.py

Controls:
    WASD        Move
    Mouse       Look around
    Space       Jump
    Left Shift  Sprint
    Left Click  Break block
    Right Click Place selected block
    1-8         Select hotbar block
    E           Open inventory and crafting screen
    F5          Save world
    F9          Load world
    Esc         Quit
"""

from ursina import *
from ursina.prefabs.first_person_controller import FirstPersonController
from collections import deque
import json
import math
import os
import random


# ------------------------------------------------------------
# Basic game settings
# ------------------------------------------------------------

APP_TITLE = "Voxel Survival Prototype"
SAVE_FILE = "voxel_world_save.json"

WATER_LEVEL = 4
MAX_TERRAIN_HEIGHT = 10
WORLD_SEED = 1337
TREE_SPAWN_CHANCE = 0.025
TREE_MIN_SPACING = 5

NORMAL_SPEED = 5.5
SPRINT_SPEED = 9.0
REACH_DISTANCE = 6
CEILING_COLLISION_MARGIN = 0.02

DAY_LENGTH_SECONDS = 90.0
UI_REFRESH_SECONDS = 0.1
CHUNK_SIZE = 16
RENDER_DISTANCE = 2
COLLIDER_DISTANCE = 1
GENERATION_DISTANCE = RENDER_DISTANCE + 1
CHUNK_STREAM_UPDATE_SECONDS = 0.25
MAX_CHUNK_GENERATIONS_PER_FRAME = 1
MAX_CHUNK_REBUILDS_PER_FRAME = 2
MAX_CHUNK_UNLOADS_PER_FRAME = 2
MIN_RENDER_DISTANCE = 1
MAX_RENDER_DISTANCE = 5
MIN_COLLIDER_DISTANCE = 1
MIN_CHUNK_GENERATIONS_PER_FRAME = 1
MAX_CHUNK_GENERATIONS_SETTING = 3
MIN_CHUNK_REBUILDS_PER_FRAME = 1
MAX_CHUNK_REBUILDS_SETTING = 4
MIN_CHUNK_UNLOADS_PER_FRAME = 1
MAX_CHUNK_UNLOADS_SETTING = 6
MOUSE_SENSITIVITY = 40
MOUSE_SENSITIVITY_STEP = 5
MIN_MOUSE_SENSITIVITY = 10
MAX_MOUSE_SENSITIVITY = 80

random.seed(WORLD_SEED)


def rgb255(r, g, b):
    """Create an Ursina color from familiar 0-255 RGB values."""
    return color.rgb(r / 255, g / 255, b / 255)


def rgba255(r, g, b, a):
    """Create an Ursina color from familiar 0-255 RGBA values."""
    return color.rgba(r / 255, g / 255, b / 255, a / 255)


# ------------------------------------------------------------
# Ursina app setup
# ------------------------------------------------------------

app = Ursina(development_mode=False)
window.title = APP_TITLE
window.borderless = False
window.exit_button.visible = False
window.fps_counter.enabled = True
window.color = rgb255(135, 206, 235)


# ------------------------------------------------------------
# Block definitions
# ------------------------------------------------------------

BLOCK_ORDER = [
    "grass",
    "dirt",
    "stone",
    "sand",
    "wood",
    "leaves",
    "water",
    "glass",
]

BLOCK_COLORS = {
    "grass": rgb255(80, 180, 70),
    "dirt": rgb255(120, 72, 35),
    "stone": rgb255(110, 110, 115),
    "sand": rgb255(220, 205, 130),
    "wood": rgb255(125, 75, 35),
    "leaves": rgb255(45, 140, 55),
    "water": rgba255(55, 120, 230, 130),
    "glass": rgba255(200, 240, 255, 115),
}

TRANSPARENT_BLOCKS = {"water", "glass", "leaves"}

# Neighbor offsets used to decide whether a block has a visible face.
NEIGHBOR_OFFSETS = [
    (1, 0, 0),
    (-1, 0, 0),
    (0, 1, 0),
    (0, -1, 0),
    (0, 0, 1),
    (0, 0, -1),
]

# world_data stores the actual saveable world:
# key: (x, y, z), value: block type string
world_data = {}

# world_data and chunk_blocks remain in memory when meshes are unloaded.
# chunks contains only active/rendered mesh entities.
chunk_blocks = {}
chunks = {}
generated_chunks = set()
dirty_chunk_queue = deque()
dirty_chunks = set()
chunk_generation_queue = deque()
queued_chunk_generations = set()
desired_render_chunks = set()
desired_collider_chunks = set()
desired_generation_chunks = set()
chunk_collider_states = {}

inventory = {
    "grass": 10,
    "dirt": 20,
    "stone": 10,
    "sand": 10,
    "wood": 5,
    "leaves": 0,
    "water": 0,
    "glass": 0,
}

selected_index = 0
health = 100.0
hunger = 100.0
inventory_open = False
crafting_grid = [None, None, None, None]
held_crafting_item = None
highlighted_block_coord = None
game_state = "main_menu"
settings_return_state = "main_menu"
debug_text_enabled = True
day_timer = 0.0
status_message_timer = 0.0
ui_update_timer = 0.0
chunk_stream_update_timer = 0.0
last_player_chunk = None
world_initialized = False


# ------------------------------------------------------------
# Simple deterministic value noise for procedural terrain
# This avoids needing extra noise/perlin packages.
# ------------------------------------------------------------

def smoothstep(t):
    """Smooth interpolation curve."""
    return t * t * (3 - 2 * t)


def lerp_float(a, b, t):
    """Linear interpolation for numbers."""
    return a + (b - a) * t


def hash_2d(x, z, seed=WORLD_SEED):
    """Deterministic pseudo-random value for a 2D grid point."""
    n = x * 374761393 + z * 668265263 + seed * 1442695041
    n = (n ^ (n >> 13)) * 1274126177
    n = n ^ (n >> 16)
    return (n & 0xFFFFFFFF) / 0xFFFFFFFF


def value_noise_2d(x, z):
    """Smooth 2D value noise."""
    x0 = math.floor(x)
    z0 = math.floor(z)
    x1 = x0 + 1
    z1 = z0 + 1

    sx = smoothstep(x - x0)
    sz = smoothstep(z - z0)

    n00 = hash_2d(x0, z0)
    n10 = hash_2d(x1, z0)
    n01 = hash_2d(x0, z1)
    n11 = hash_2d(x1, z1)

    ix0 = lerp_float(n00, n10, sx)
    ix1 = lerp_float(n01, n11, sx)
    return lerp_float(ix0, ix1, sz)


def fbm_noise(x, z, octaves=4):
    """Fractal Brownian motion noise for more natural terrain."""
    total = 0.0
    amplitude = 1.0
    frequency = 1.0
    max_value = 0.0

    for _ in range(octaves):
        total += value_noise_2d(x * frequency, z * frequency) * amplitude
        max_value += amplitude
        amplitude *= 0.5
        frequency *= 2.0

    return total / max_value


def terrain_height(x, z):
    """Return the terrain height for a world x/z coordinate."""
    base = fbm_noise(x * 0.075, z * 0.075, octaves=5)
    hills = fbm_noise((x + 100) * 0.14, (z - 100) * 0.14, octaves=3)
    height = int(3 + base * 5 + hills * 3)
    return max(1, min(MAX_TERRAIN_HEIGHT, height))


# ------------------------------------------------------------
# Visible-face mesh rendering
# ------------------------------------------------------------

# Each tuple contains the neighboring block offset, face vertices, and normal.
# Vertices are ordered counter-clockwise from outside the block.
FACE_DEFINITIONS = [
    ((1, 0, 0), ((0.5, -0.5, -0.5), (0.5, 0.5, -0.5), (0.5, 0.5, 0.5), (0.5, -0.5, 0.5)), (1, 0, 0)),
    ((-1, 0, 0), ((-0.5, -0.5, -0.5), (-0.5, -0.5, 0.5), (-0.5, 0.5, 0.5), (-0.5, 0.5, -0.5)), (-1, 0, 0)),
    ((0, 1, 0), ((-0.5, 0.5, -0.5), (-0.5, 0.5, 0.5), (0.5, 0.5, 0.5), (0.5, 0.5, -0.5)), (0, 1, 0)),
    ((0, -1, 0), ((-0.5, -0.5, -0.5), (0.5, -0.5, -0.5), (0.5, -0.5, 0.5), (-0.5, -0.5, 0.5)), (0, -1, 0)),
    ((0, 0, 1), ((-0.5, -0.5, 0.5), (0.5, -0.5, 0.5), (0.5, 0.5, 0.5), (-0.5, 0.5, 0.5)), (0, 0, 1)),
    ((0, 0, -1), ((-0.5, -0.5, -0.5), (-0.5, 0.5, -0.5), (0.5, 0.5, -0.5), (0.5, -0.5, -0.5)), (0, 0, -1)),
]


def coord_to_key(coord):
    """Convert a coordinate tuple into a JSON-safe string."""
    x, y, z = coord
    return f"{int(x)},{int(y)},{int(z)}"


def key_to_coord(key):
    """Convert a saved coordinate string back into a tuple."""
    x, y, z = key.split(",")
    return int(x), int(y), int(z)


def chunk_coord_to_key(chunk_coord):
    """Convert a horizontal chunk coordinate into a JSON-safe string."""
    chunk_x, chunk_z = chunk_coord
    return f"{int(chunk_x)},{int(chunk_z)}"


def key_to_chunk_coord(key):
    """Convert a saved chunk coordinate string back into a tuple."""
    chunk_x, chunk_z = key.split(",")
    return int(chunk_x), int(chunk_z)


def neighbor_coords(coord):
    """Yield coordinates directly adjacent to a block."""
    x, y, z = coord
    for dx, dy, dz in NEIGHBOR_OFFSETS:
        yield x + dx, y + dy, z + dz


def should_render_face(block_type, neighbor_type):
    """Return whether a face is visible beside the neighboring block."""
    if neighbor_type is None:
        return True

    return neighbor_type in TRANSPARENT_BLOCKS and neighbor_type != block_type


def chunk_coord_from_block(coord):
    """Return the horizontal chunk containing a world block coordinate."""
    return (
        int(math.floor(coord[0] / CHUNK_SIZE)),
        int(math.floor(coord[2] / CHUNK_SIZE)),
    )


def index_block_in_chunk(coord):
    """Add a world block coordinate to its chunk index."""
    chunk_coord = chunk_coord_from_block(coord)
    chunk_blocks.setdefault(chunk_coord, set()).add(coord)


def remove_block_from_chunk_index(coord):
    """Remove a world block coordinate from its chunk index."""
    chunk_coord = chunk_coord_from_block(coord)
    coords = chunk_blocks.get(chunk_coord)
    if coords is None:
        return

    coords.discard(coord)
    if not coords:
        chunk_blocks.pop(chunk_coord)


def mark_chunk_dirty(chunk_coord):
    """Queue a chunk rebuild once, even if several edits touch it."""
    if chunk_coord in chunks and chunk_coord not in dirty_chunks:
        dirty_chunks.add(chunk_coord)
        dirty_chunk_queue.append(chunk_coord)


def mark_affected_chunks_dirty(coord):
    """Dirty an edited chunk and neighbors when an edit touches its border."""
    x, _, z = coord
    chunk_x, chunk_z = chunk_coord_from_block(coord)
    mark_chunk_dirty((chunk_x, chunk_z))

    if x % CHUNK_SIZE == 0:
        mark_chunk_dirty((chunk_x - 1, chunk_z))
    if x % CHUNK_SIZE == CHUNK_SIZE - 1:
        mark_chunk_dirty((chunk_x + 1, chunk_z))
    if z % CHUNK_SIZE == 0:
        mark_chunk_dirty((chunk_x, chunk_z - 1))
    if z % CHUNK_SIZE == CHUNK_SIZE - 1:
        mark_chunk_dirty((chunk_x, chunk_z + 1))


def build_chunk_mesh(chunk_coord, block_types):
    """Build visible faces for one chunk and one transparency group."""
    vertices = []
    triangles = []
    colors = []
    normals = []

    for x, y, z in chunk_blocks.get(chunk_coord, ()):
        block_type = world_data[(x, y, z)]
        if block_type not in block_types:
            continue

        block_color = BLOCK_COLORS.get(block_type, color.white)

        for (dx, dy, dz), face_vertices, normal in FACE_DEFINITIONS:
            neighbor_type = world_data.get((x + dx, y + dy, z + dz))
            if not should_render_face(block_type, neighbor_type):
                continue

            vertex_index = len(vertices)
            vertices.extend(
                (x + vx, y + vy, z + vz)
                for vx, vy, vz in face_vertices
            )
            triangles.extend(
                (
                    (vertex_index, vertex_index + 2, vertex_index + 1),
                    (vertex_index, vertex_index + 3, vertex_index + 2),
                )
            )
            colors.extend([block_color] * 4)
            normals.extend([normal] * 4)

    return Mesh(
        vertices=vertices,
        triangles=triangles,
        colors=colors,
        normals=normals,
        static=True,
    )


def rebuild_chunk(chunk_coord):
    """Replace both combined mesh entities belonging to one chunk."""
    if chunk_coord not in chunks:
        return

    for entity in chunks[chunk_coord]:
        destroy(entity)

    entities = []
    collider_type = "mesh" if chunk_coord in desired_collider_chunks else None

    opaque_blocks = set(BLOCK_ORDER) - TRANSPARENT_BLOCKS
    opaque_mesh = build_chunk_mesh(chunk_coord, opaque_blocks)
    if opaque_mesh.vertices:
        entities.append(
            Entity(
                parent=scene,
                model=opaque_mesh,
                collider=collider_type,
                chunk_coord=chunk_coord,
                chunk_mesh_type="opaque",
                is_chunk_mesh=True,
            )
        )

    transparent_mesh = build_chunk_mesh(chunk_coord, TRANSPARENT_BLOCKS)
    if transparent_mesh.vertices:
        entities.append(
            Entity(
                parent=scene,
                model=transparent_mesh,
                collider=collider_type,
                double_sided=True,
                chunk_coord=chunk_coord,
                chunk_mesh_type="transparent",
                is_chunk_mesh=True,
            )
        )

    if entities:
        chunks[chunk_coord] = entities
    else:
        chunks[chunk_coord] = []
    chunk_collider_states[chunk_coord] = collider_type is not None


def rebuild_dirty_chunks():
    """Rebuild a small number of queued chunks during each rendered frame."""
    for _ in range(MAX_CHUNK_REBUILDS_PER_FRAME):
        if not dirty_chunk_queue:
            return

        chunk_coord = dirty_chunk_queue.popleft()
        dirty_chunks.discard(chunk_coord)
        if chunk_coord in chunks:
            rebuild_chunk(chunk_coord)


def destroy_all_chunk_meshes():
    """Unload every visual chunk while retaining the world block data."""
    for entities in chunks.values():
        for entity in entities:
            destroy(entity)

    chunks.clear()
    chunk_collider_states.clear()
    dirty_chunk_queue.clear()
    dirty_chunks.clear()


def activate_chunk(chunk_coord, immediate=False):
    """Load a generated chunk visually, optionally building it immediately."""
    if chunk_coord not in generated_chunks or chunk_coord in chunks:
        return

    chunks[chunk_coord] = []
    if immediate:
        rebuild_chunk(chunk_coord)
    else:
        mark_chunk_dirty(chunk_coord)


def unload_chunk(chunk_coord):
    """Destroy a distant chunk's visuals without discarding its blocks."""
    for entity in chunks.pop(chunk_coord, ()):
        destroy(entity)

    chunk_collider_states.pop(chunk_coord, None)
    dirty_chunks.discard(chunk_coord)


def queue_chunk_generation(chunk_coord):
    """Queue procedural generation once for an unknown chunk."""
    if (
        chunk_coord not in generated_chunks
        and chunk_coord not in queued_chunk_generations
    ):
        queued_chunk_generations.add(chunk_coord)
        chunk_generation_queue.append(chunk_coord)


def add_block(coord, block_type, create_entity=True):
    """Add a block to world data and optionally create its visible entity."""
    coord = (int(coord[0]), int(coord[1]), int(coord[2]))

    if coord in world_data:
        return False

    world_data[coord] = block_type
    index_block_in_chunk(coord)

    if create_entity:
        mark_affected_chunks_dirty(coord)

    return True


def remove_block(coord):
    """Remove a block from the world."""
    coord = (int(coord[0]), int(coord[1]), int(coord[2]))

    if coord not in world_data:
        return False

    world_data.pop(coord)
    remove_block_from_chunk_index(coord)
    mark_affected_chunks_dirty(coord)

    return True


# ------------------------------------------------------------
# Procedural world generation
# ------------------------------------------------------------

def tree_candidate_score(x, z):
    """Return a deterministic tree candidate score, or None for no tree."""
    score = hash_2d(x * 3 + 7, z * 3 - 9)
    if score >= TREE_SPAWN_CHANCE:
        return None

    if terrain_height(x, z) <= WATER_LEVEL + 1:
        return None

    return score


def should_generate_tree(x, z):
    """Keep only the strongest deterministic tree candidate in each area."""
    score = tree_candidate_score(x, z)
    if score is None:
        return False

    for offset_x in range(-TREE_MIN_SPACING, TREE_MIN_SPACING + 1):
        for offset_z in range(-TREE_MIN_SPACING, TREE_MIN_SPACING + 1):
            if offset_x == 0 and offset_z == 0:
                continue

            if offset_x * offset_x + offset_z * offset_z > TREE_MIN_SPACING ** 2:
                continue

            neighbor_x = x + offset_x
            neighbor_z = z + offset_z
            neighbor_score = tree_candidate_score(neighbor_x, neighbor_z)
            if neighbor_score is None:
                continue

            if neighbor_score < score:
                return False

            if neighbor_score == score and (neighbor_x, neighbor_z) < (x, z):
                return False

    return True


def generate_tree(x, y, z):
    """Generate a small voxel tree at the given position."""
    trunk_height = 3 + int(hash_2d(x + 50, z - 50) * 3)

    # Trunk
    for i in range(trunk_height):
        add_block((x, y + i, z), "wood", create_entity=False)

    # Leaves blob
    leaf_center_y = y + trunk_height
    for lx in range(-2, 3):
        for ly in range(-1, 3):
            for lz in range(-2, 3):
                distance = abs(lx) + abs(ly) + abs(lz)
                if distance <= 4:
                    pos = (x + lx, leaf_center_y + ly, z + lz)
                    if pos not in world_data:
                        add_block(pos, "leaves", create_entity=False)


def generate_chunk(chunk_coord):
    """Generate one deterministic terrain chunk and retain its block data."""
    if chunk_coord in generated_chunks:
        return

    chunk_x, chunk_z = chunk_coord
    start_x = chunk_x * CHUNK_SIZE
    start_z = chunk_z * CHUNK_SIZE

    for x in range(start_x, start_x + CHUNK_SIZE):
        for z in range(start_z, start_z + CHUNK_SIZE):
            h = terrain_height(x, z)

            # Choose surface block.
            if h <= WATER_LEVEL + 1:
                surface_block = "sand"
            else:
                surface_block = "grass"

            # Terrain column.
            for y in range(0, h + 1):
                if y == h:
                    block_type = surface_block
                elif y >= h - 3:
                    block_type = "dirt"
                else:
                    block_type = "stone"

                coord = (x, y, z)
                if coord not in world_data:
                    add_block(coord, block_type, create_entity=False)

            # Fill shallow areas with water.
            if h < WATER_LEVEL:
                for wy in range(h + 1, WATER_LEVEL + 1):
                    add_block((x, wy, z), "water", create_entity=False)

            # Natural trees are seed-based and spaced independently of chunk
            # generation order so streaming cannot change their layout.
            if surface_block == "grass" and should_generate_tree(x, z):
                generate_tree(x, h + 1, z)

    generated_chunks.add(chunk_coord)

    # Generation can expose or cover faces along an already rendered border.
    chunk_x, chunk_z = chunk_coord
    for affected_chunk in (
        (chunk_x, chunk_z),
        (chunk_x - 1, chunk_z),
        (chunk_x + 1, chunk_z),
        (chunk_x, chunk_z - 1),
        (chunk_x, chunk_z + 1),
    ):
        mark_chunk_dirty(affected_chunk)


def generate_initial_world():
    """Generate a small safe starting area when singleplayer begins."""
    global last_player_chunk

    world_data.clear()
    chunk_blocks.clear()
    generated_chunks.clear()
    destroy_all_chunk_meshes()
    chunk_generation_queue.clear()
    queued_chunk_generations.clear()
    desired_render_chunks.clear()
    desired_collider_chunks.clear()
    desired_generation_chunks.clear()
    last_player_chunk = None

    for chunk_x in range(-1, 2):
        for chunk_z in range(-1, 2):
            generate_chunk((chunk_x, chunk_z))


def chunk_square(center, distance):
    """Return chunks in a square radius sorted nearest-first."""
    center_x, center_z = center
    coords = [
        (center_x + dx, center_z + dz)
        for dx in range(-distance, distance + 1)
        for dz in range(-distance, distance + 1)
    ]
    return sorted(
        coords,
        key=lambda coord: (
            max(abs(coord[0] - center_x), abs(coord[1] - center_z)),
            abs(coord[0] - center_x) + abs(coord[1] - center_z),
        ),
    )


def refresh_chunk_collider_targets(immediate_player_chunk=False):
    """Queue collider changes while immediately protecting the current chunk."""
    player_chunk = chunk_coord_from_block((player.x, 0, player.z))

    for chunk_coord in list(chunks):
        collider_enabled = chunk_coord in desired_collider_chunks
        if chunk_collider_states.get(chunk_coord, False) == collider_enabled:
            continue

        if immediate_player_chunk and chunk_coord == player_chunk:
            rebuild_chunk(chunk_coord)
        else:
            mark_chunk_dirty(chunk_coord)


def schedule_chunks_around_player(force=False):
    """Queue nearby generation, rendering, and collider updates around the player."""
    global desired_render_chunks, desired_collider_chunks
    global desired_generation_chunks, last_player_chunk

    player_chunk = chunk_coord_from_block((player.x, 0, player.z))
    if not force and player_chunk == last_player_chunk:
        return

    last_player_chunk = player_chunk
    desired_render_chunks = set(chunk_square(player_chunk, RENDER_DISTANCE))
    desired_collider_chunks = set(chunk_square(player_chunk, COLLIDER_DISTANCE))
    desired_generation_chunks = set(chunk_square(player_chunk, GENERATION_DISTANCE))

    # Reprioritise pending work so stale requests never delay nearby terrain.
    chunk_generation_queue.clear()
    queued_chunk_generations.clear()
    for chunk_coord in chunk_square(player_chunk, GENERATION_DISTANCE):
        queue_chunk_generation(chunk_coord)

    for chunk_coord in desired_render_chunks:
        activate_chunk(chunk_coord)

    refresh_chunk_collider_targets(immediate_player_chunk=True)


def process_chunk_streaming():
    """Spread generation, visual loading, and unloading across frames."""
    unloaded = 0
    for chunk_coord in list(chunks):
        if chunk_coord not in desired_render_chunks:
            unload_chunk(chunk_coord)
            unloaded += 1
            if unloaded >= MAX_CHUNK_UNLOADS_PER_FRAME:
                break

    for _ in range(MAX_CHUNK_GENERATIONS_PER_FRAME):
        if not chunk_generation_queue:
            break

        chunk_coord = chunk_generation_queue.popleft()
        queued_chunk_generations.discard(chunk_coord)
        generate_chunk(chunk_coord)

        if chunk_coord in desired_render_chunks:
            activate_chunk(chunk_coord)


# ------------------------------------------------------------
# Save and load
# ------------------------------------------------------------

def save_world():
    """Save chunk-grouped world data, inventory, stats, and player position."""
    saved_chunks = {}
    for chunk_coord, coords in chunk_blocks.items():
        saved_chunks[chunk_coord_to_key(chunk_coord)] = {
            coord_to_key(coord): world_data[coord]
            for coord in coords
        }

    save_data = {
        "format_version": 2,
        "chunks": saved_chunks,
        "generated_chunks": [list(coord) for coord in sorted(generated_chunks)],
        "inventory": inventory,
        "selected_index": selected_index,
        "health": health,
        "hunger": hunger,
        "player_position": [
            round(player.x, 3),
            round(player.y, 3),
            round(player.z, 3),
        ],
    }

    with open(SAVE_FILE, "w", encoding="utf-8") as file:
        json.dump(save_data, file, indent=2)

    set_status(f"Saved to {SAVE_FILE}")


def load_world():
    """Load chunk-grouped world data and restore nearby rendered chunks."""
    global selected_index, health, hunger, last_player_chunk, world_initialized

    if not os.path.exists(SAVE_FILE):
        set_status("No save file found.")
        return False

    with open(SAVE_FILE, "r", encoding="utf-8") as file:
        save_data = json.load(file)

    world_data.clear()
    chunk_blocks.clear()
    generated_chunks.clear()
    destroy_all_chunk_meshes()
    chunk_generation_queue.clear()
    queued_chunk_generations.clear()
    desired_render_chunks.clear()
    desired_collider_chunks.clear()
    desired_generation_chunks.clear()
    last_player_chunk = None

    saved_chunks = save_data.get("chunks")
    if saved_chunks is not None:
        for chunk_key, saved_blocks in saved_chunks.items():
            chunk_coord = key_to_chunk_coord(chunk_key)
            for key, block_type in saved_blocks.items():
                coord = key_to_coord(key)
                world_data[coord] = block_type
                chunk_blocks.setdefault(chunk_coord, set()).add(coord)
    else:
        # Backward compatibility for saves created before chunk-grouped storage.
        saved_world = save_data.get("world", {})
        for key, block_type in saved_world.items():
            coord = key_to_coord(key)
            world_data[coord] = block_type
            index_block_in_chunk(coord)

    saved_generated_chunks = save_data.get("generated_chunks")
    if saved_generated_chunks is None:
        generated_chunks.update(chunk_blocks)
    else:
        generated_chunks.update(tuple(coord) for coord in saved_generated_chunks)

    saved_inventory = save_data.get("inventory", {})
    for block_type in BLOCK_ORDER:
        inventory[block_type] = int(saved_inventory.get(block_type, inventory.get(block_type, 0)))

    selected_index = int(save_data.get("selected_index", 0))
    selected_index = max(0, min(selected_index, len(BLOCK_ORDER) - 1))

    health = float(save_data.get("health", 100))
    hunger = float(save_data.get("hunger", 100))

    pos = save_data.get("player_position", [0, 15, 0])
    player.position = Vec3(pos[0], pos[1], pos[2])

    schedule_chunks_around_player(force=True)
    activate_chunk(chunk_coord_from_block((player.x, 0, player.z)), immediate=True)
    world_initialized = True
    update_ui()
    set_status(f"Loaded {SAVE_FILE}")
    return True


# ------------------------------------------------------------
# Player setup
# ------------------------------------------------------------

def find_safe_spawn():
    """Find a safe spawn point near the center of the map."""
    best_x, best_z = 0, 0
    best_y = terrain_height(0, 0) + 4

    for x in range(-6, 7):
        for z in range(-6, 7):
            h = terrain_height(x, z)
            spawn_y = h + 3

            # Leave room around the player's body and camera. Trees are
            # generated before spawning, so checking world_data avoids
            # starting inside a trunk or leaf canopy.
            clearance = (
                (px, py, pz)
                for px in range(x - 3, x + 4)
                for py in range(spawn_y - 1, spawn_y + 4)
                for pz in range(z - 3, z + 4)
            )

            if h > WATER_LEVEL and all(coord not in world_data for coord in clearance):
                return Vec3(x, spawn_y, z)

    return Vec3(best_x, best_y, best_z)


player = FirstPersonController(
    position=(0, 15, 0),
    speed=NORMAL_SPEED,
    jump_height=1.5,
    gravity=0.7,
)

player.cursor.visible = False
player.mouse_sensitivity = Vec2(MOUSE_SENSITIVITY, MOUSE_SENSITIVITY)
mouse.locked = False


player_controller_update = player.update
player_controller_input = player.input


def update_player_controller():
    """Run first-person movement only while gameplay input is active."""
    if game_state == "playing" and not inventory_open:
        player_controller_update()


def input_player_controller(key):
    """Prevent controller actions while gameplay input is inactive."""
    if game_state == "playing" and not inventory_open:
        player_controller_input(key)


player.update = update_player_controller
player.input = input_player_controller


# ------------------------------------------------------------
# Lighting and sky
# ------------------------------------------------------------

sky = Sky()
sun = DirectionalLight(shadows=False)
sun.look_at(Vec3(1, -1, -1))

ambient = AmbientLight()
ambient.color = rgba255(120, 120, 120, 255)


# ------------------------------------------------------------
# Crafting
# ------------------------------------------------------------

# Slots are stored row by row: top-left, top-right, bottom-left, bottom-right.
CRAFTING_RECIPES = {
    ("sand", "sand", "stone", None): {
        "result": ("glass", 2),
        "message": "Crafted 2 glass.",
    },
    ("leaves", "leaves", "leaves", "leaves"): {
        "result": ("wood", 1),
        "message": "Crafted 1 wood from leaves.",
    },
    ("dirt", "dirt", "dirt", "dirt"): {
        "result": ("stone", 1),
        "message": "Compressed 4 dirt into 1 stone.",
    },
}


def get_matching_recipe():
    """Return the recipe matching the exact 2x2 crafting pattern."""
    return CRAFTING_RECIPES.get(tuple(crafting_grid))


def select_inventory_item(index):
    """Pick up one inventory item for crafting and select its hotbar slot."""
    global selected_index, held_crafting_item

    selected_index = index
    block_type = BLOCK_ORDER[index]

    if held_crafting_item is not None:
        set_status("Place or return the held crafting item first.")
    elif inventory.get(block_type, 0) <= 0:
        set_status(f"No {block_type} available.")
    else:
        inventory[block_type] -= 1
        held_crafting_item = block_type
        set_status(f"Holding 1 {block_type}. Click a crafting slot.")

    update_ui()


def click_crafting_slot(index):
    """Place, pick up, or swap one item in a crafting input slot."""
    global held_crafting_item

    slot_item = crafting_grid[index]
    if held_crafting_item is None:
        held_crafting_item = slot_item
        crafting_grid[index] = None
    elif slot_item is None:
        crafting_grid[index] = held_crafting_item
        held_crafting_item = None
    else:
        crafting_grid[index] = held_crafting_item
        held_crafting_item = slot_item

    update_ui()


def collect_crafting_output():
    """Collect one crafted result and consume the matching grid pattern."""
    recipe = get_matching_recipe()
    if recipe is None:
        set_status("The crafting grid does not match a recipe.")
        return

    result_item, result_amount = recipe["result"]
    inventory[result_item] = inventory.get(result_item, 0) + result_amount

    for index in range(len(crafting_grid)):
        crafting_grid[index] = None

    set_status(recipe["message"])
    update_ui()


def return_crafting_items():
    """Return unfinished grid items to inventory when the screen closes."""
    global held_crafting_item

    for index, block_type in enumerate(crafting_grid):
        if block_type is not None:
            inventory[block_type] = inventory.get(block_type, 0) + 1
            crafting_grid[index] = None

    if held_crafting_item is not None:
        inventory[held_crafting_item] = inventory.get(held_crafting_item, 0) + 1
        held_crafting_item = None


# ------------------------------------------------------------
# UI setup
# ------------------------------------------------------------

UI_DARK = rgba255(13, 17, 22, 230)
UI_PANEL = rgba255(35, 43, 52, 248)
UI_PANEL_BORDER = rgba255(104, 86, 60, 255)
UI_SLOT = rgba255(53, 62, 72, 255)
UI_SLOT_HOVER = rgba255(76, 96, 116, 255)
UI_SELECTED = rgba255(218, 184, 72, 255)
UI_TEXT = rgba255(235, 238, 235, 255)
UI_MUTED_TEXT = rgba255(170, 184, 194, 255)
UI_DANGER = rgba255(182, 66, 58, 255)
UI_BLUE = rgba255(66, 106, 142, 255)
UI_DIM = rgba255(70, 74, 78, 180)


def create_panel(parent, position, scale):
    """Create a dark voxel-style panel with a muted brown frame."""
    frame = Entity(
        parent=parent,
        model="quad",
        color=UI_PANEL_BORDER,
        position=position,
        scale=scale,
        z=0.10,
    )
    frame.inner = Entity(
        parent=frame,
        model="quad",
        color=UI_PANEL,
        scale=(0.985, 0.975),
        z=-0.005,
    )
    return frame


def create_framed_button(parent, text, position, scale):
    """Create one consistently framed interactive button."""
    frame = Entity(
        parent=parent,
        model="quad",
        color=UI_PANEL_BORDER,
        position=position,
        scale=scale,
        z=0.04,
    )
    button = Button(
        text=text,
        parent=frame,
        color=UI_SLOT,
        highlight_color=UI_BLUE,
        pressed_color=UI_SELECTED,
        scale=(0.96, 0.82),
        z=-0.01,
    )
    button.frame = frame
    return button


def create_slot(parent, position, scale):
    """Create a square inventory or hotbar slot with a visible border."""
    frame = Entity(
        parent=parent,
        model="quad",
        color=UI_PANEL_BORDER,
        position=position,
        scale=scale,
        z=0.04,
    )
    slot = Button(
        text="",
        parent=frame,
        color=UI_SLOT,
        highlight_color=UI_SLOT_HOVER,
        pressed_color=UI_SELECTED,
        scale=(0.90, 0.90),
        z=-0.01,
    )
    slot.frame = frame
    return slot


def create_label(parent, text, position, scale=1.0, color_value=UI_TEXT, origin=(-0.5, 0)):
    """Create a styled UI text label."""
    return Text(
        text=text,
        parent=parent,
        position=position,
        scale=scale,
        color=color_value,
        origin=origin,
    )


def create_health_icon(parent, position):
    """Create one small block-built health icon without external textures."""
    icon = Entity(parent=parent, position=position, scale=(0.018, 0.018))
    icon.parts = [
        Entity(parent=icon, model="quad", position=(-0.24, 0.20), scale=(0.44, 0.44)),
        Entity(parent=icon, model="quad", position=(0.24, 0.20), scale=(0.44, 0.44)),
        Entity(parent=icon, model="quad", position=(0, -0.05), scale=(0.78, 0.52)),
        Entity(parent=icon, model="quad", position=(0, -0.40), scale=(0.34, 0.24)),
    ]
    return icon


def create_food_icon(parent, position):
    """Create one small block-built food icon without external textures."""
    icon = Entity(parent=parent, position=position, scale=(0.018, 0.018))
    icon.parts = [
        Entity(parent=icon, model="quad", position=(-0.08, 0.08), scale=(0.62, 0.72), rotation_z=-32),
        Entity(parent=icon, model="quad", position=(0.30, -0.26), scale=(0.18, 0.48), rotation_z=-32),
        Entity(parent=icon, model="quad", position=(0.46, -0.42), scale=(0.30, 0.18), rotation_z=-32),
    ]
    return icon


def set_icon_color(icon, color_value):
    """Apply one fill or dim color to every primitive in an icon."""
    for part in icon.parts:
        part.color = color_value


crosshair_horizontal = Entity(
    parent=camera.ui,
    model="quad",
    color=rgba255(245, 245, 240, 220),
    scale=(0.014, 0.0015),
    position=(0, 0, 0),
)

crosshair_vertical = Entity(
    parent=camera.ui,
    model="quad",
    color=rgba255(245, 245, 240, 220),
    scale=(0.0015, 0.014),
    position=(0, 0, 0),
)

selected_text = create_label(
    camera.ui,
    text="",
    position=(-0.18, -0.335),
    scale=0.92,
    color_value=UI_TEXT,
)

status_text = create_label(
    camera.ui,
    text="",
    position=(-0.87, 0.43),
    scale=0.92,
    color_value=UI_TEXT,
)

help_text = create_label(
    camera.ui,
    text="E Inventory  |  Esc Pause",
    position=(-0.11, 0.465),
    scale=0.72,
    color_value=UI_MUTED_TEXT,
)

coordinate_text = create_label(
    camera.ui,
    text="",
    position=(0.48, 0.44),
    scale=0.62,
    color_value=UI_MUTED_TEXT,
)

survival_panel = create_panel(
    camera.ui,
    position=(-0.72, 0.405),
    scale=(0.34, 0.13),
)

health_label = create_label(
    camera.ui,
    text="HP",
    position=(-0.87, 0.43),
    scale=0.72,
    color_value=UI_MUTED_TEXT,
)

hunger_label = create_label(
    camera.ui,
    text="FOOD",
    position=(-0.87, 0.385),
    scale=0.64,
    color_value=UI_MUTED_TEXT,
)

health_icons = []
hunger_icons = []

for i in range(10):
    x_pos = -0.79 + i * 0.029
    health_icons.append(create_health_icon(camera.ui, (x_pos, 0.43)))
    hunger_icons.append(create_food_icon(camera.ui, (x_pos, 0.385)))

hotbar_panel = create_panel(camera.ui, position=(0, -0.415), scale=(0.73, 0.115))
hotbar_slots = []
hotbar_texts = []

for i, block_type in enumerate(BLOCK_ORDER):
    x_pos = -0.315 + i * 0.09
    slot = create_slot(camera.ui, position=(x_pos, -0.415), scale=(0.078, 0.088))
    label = create_label(
        camera.ui,
        text="",
        position=(x_pos - 0.028, -0.438),
        scale=0.57,
        color_value=UI_TEXT,
    )
    hotbar_slots.append(slot)
    hotbar_texts.append(label)


inventory_screen = Entity(parent=camera.ui, enabled=False)

inventory_backdrop = Entity(
    parent=inventory_screen,
    model="quad",
    color=rgba255(3, 6, 9, 190),
    scale=(2, 1),
    z=0.20,
)

inventory_panel = create_panel(
    inventory_screen,
    position=(0, 0),
    scale=(1.62, 0.89),
)

inventory_title_bar = Entity(
    parent=inventory_screen,
    model="quad",
    color=rgba255(57, 48, 39, 255),
    position=(0, 0.39),
    scale=(1.57, 0.075),
)

inventory_title = create_label(
    inventory_screen,
    text="INVENTORY",
    position=(-0.73, 0.372),
    scale=1.18,
    color_value=UI_TEXT,
)

inventory_close_button = create_framed_button(
    inventory_screen,
    text="X",
    position=(0.74, 0.39),
    scale=(0.07, 0.05),
)
inventory_close_button.on_click = lambda: set_inventory_open(False)

inventory_hint = create_label(
    inventory_screen,
    text="Click item -> place in crafting grid -> collect output  |  E or Esc closes",
    position=(-0.72, -0.405),
    scale=0.64,
    color_value=UI_MUTED_TEXT,
)

character_panel = create_panel(
    inventory_screen,
    position=(-0.53, 0.04),
    scale=(0.31, 0.57),
)
character_title = create_label(
    inventory_screen,
    text="SURVIVOR",
    position=(-0.665, 0.285),
    scale=0.72,
    color_value=UI_MUTED_TEXT,
)
character_head = Entity(
    parent=inventory_screen,
    model="quad",
    color=rgba255(137, 112, 78, 255),
    position=(-0.53, 0.15),
    scale=(0.08, 0.08),
)
character_body = Entity(
    parent=inventory_screen,
    model="quad",
    color=UI_BLUE,
    position=(-0.53, 0.025),
    scale=(0.13, 0.15),
)
character_left_leg = Entity(
    parent=inventory_screen,
    model="quad",
    color=rgba255(70, 77, 86, 255),
    position=(-0.57, -0.13),
    scale=(0.045, 0.15),
)
character_right_leg = Entity(
    parent=inventory_screen,
    model="quad",
    color=rgba255(70, 77, 86, 255),
    position=(-0.49, -0.13),
    scale=(0.045, 0.15),
)

equipment_title = create_label(
    inventory_screen,
    text="EQUIPMENT",
    position=(-0.78, 0.285),
    scale=0.61,
    color_value=UI_MUTED_TEXT,
)
equipment_slots = []
for i, label in enumerate(("Head", "Chest", "Legs", "Boots")):
    slot = create_slot(
        inventory_screen,
        position=(-0.73, 0.19 - i * 0.12),
        scale=(0.09, 0.09),
    )
    slot.text = label
    slot.text_entity.scale = 0.58
    equipment_slots.append(slot)

inventory_label = create_label(
    inventory_screen,
    text="BLOCK ITEMS",
    position=(-0.34, 0.285),
    scale=0.76,
    color_value=UI_MUTED_TEXT,
)
inventory_slots = []
for i, block_type in enumerate(BLOCK_ORDER):
    column = i % 4
    row = i // 4
    slot = create_slot(
        inventory_screen,
        position=(-0.27 + column * 0.13, 0.17 - row * 0.13),
        scale=(0.112, 0.105),
    )
    slot.on_click = Func(select_inventory_item, i)
    inventory_slots.append(slot)

inventory_hotbar_title = create_label(
    inventory_screen,
    text="HOTBAR",
    position=(-0.34, -0.13),
    scale=0.72,
    color_value=UI_MUTED_TEXT,
)
inventory_hotbar_slots = []
for i, block_type in enumerate(BLOCK_ORDER):
    slot = create_slot(
        inventory_screen,
        position=(-0.29 + i * 0.09, -0.235),
        scale=(0.077, 0.08),
    )
    inventory_hotbar_slots.append(slot)

crafting_panel = create_panel(
    inventory_screen,
    position=(0.51, 0.08),
    scale=(0.47, 0.47),
)
crafting_title = create_label(
    inventory_screen,
    text="CRAFTING  2x2",
    position=(0.30, 0.285),
    scale=0.78,
    color_value=UI_MUTED_TEXT,
)
crafting_slots = []
for i in range(4):
    column = i % 2
    row = i // 2
    slot = create_slot(
        inventory_screen,
        position=(0.34 + column * 0.11, 0.13 - row * 0.11),
        scale=(0.09, 0.09),
    )
    slot.on_click = Func(click_crafting_slot, i)
    crafting_slots.append(slot)

crafting_arrow = create_label(
    inventory_screen,
    text="=>",
    position=(0.54, 0.065),
    scale=1.1,
    color_value=UI_SELECTED,
)

crafting_output_slot = create_slot(
    inventory_screen,
    position=(0.67, 0.075),
    scale=(0.14, 0.13),
)
crafting_output_slot.on_click = collect_crafting_output

held_item_text = create_label(
    inventory_screen,
    text="",
    position=(-0.34, -0.335),
    scale=0.72,
    color_value=UI_SELECTED,
)

recipe_info_panel = create_panel(
    inventory_screen,
    position=(0.51, -0.245),
    scale=(0.47, 0.17),
)
recipe_hints = create_label(
    inventory_screen,
    text=(
        "RECIPE HINTS\n"
        "Glass x2: sand sand / stone empty\n"
        "Wood x1: leaves x4  |  Stone x1: dirt x4"
    ),
    position=(0.30, -0.205),
    scale=0.54,
    color_value=UI_MUTED_TEXT,
)


# ------------------------------------------------------------
# Main, pause, and settings menus
# ------------------------------------------------------------

def create_menu_button(parent, text, y_position):
    """Create one consistent menu button."""
    return create_framed_button(
        parent,
        text=text,
        position=(0, y_position),
        scale=(0.34, 0.07),
    )


main_menu_screen = Entity(parent=camera.ui, enabled=False)
main_menu_backdrop = Entity(
    parent=main_menu_screen,
    model="quad",
    color=rgba255(4, 7, 10, 205),
    scale=(2, 1),
    z=0.20,
)
main_menu_panel = create_panel(
    main_menu_screen,
    position=(0, 0),
    scale=(0.66, 0.80),
)
main_menu_title = create_label(
    main_menu_screen,
    text="VOXEL SURVIVAL",
    position=(0, 0.28),
    scale=2.15,
    color_value=UI_TEXT,
    origin=(0, 0),
)
main_menu_subtitle = create_label(
    main_menu_screen,
    text="Prototype Build  |  Python + Ursina",
    position=(0, 0.205),
    scale=0.85,
    color_value=UI_MUTED_TEXT,
    origin=(0, 0),
)
singleplayer_button = create_menu_button(main_menu_screen, ">  SINGLEPLAYER", 0.09)
multiplayer_button = create_menu_button(main_menu_screen, "@  MULTIPLAYER", 0.0)
main_settings_button = create_menu_button(main_menu_screen, "*  SETTINGS", -0.09)
main_quit_button = create_menu_button(main_menu_screen, "X  QUIT GAME", -0.18)
main_quit_button.frame.color = UI_DANGER
main_menu_version = create_label(
    main_menu_screen,
    text="v0.1  EDUCATIONAL PROTOTYPE",
    position=(0, -0.31),
    scale=0.68,
    color_value=UI_MUTED_TEXT,
    origin=(0, 0),
)

pause_menu_screen = Entity(parent=camera.ui, enabled=False)
pause_menu_backdrop = Entity(
    parent=pause_menu_screen,
    model="quad",
    color=rgba255(0, 0, 0, 185),
    scale=(2, 1),
    z=0.20,
)
pause_menu_panel = create_panel(
    pause_menu_screen,
    position=(-0.18, 0),
    scale=(0.58, 0.80),
)
pause_menu_title = create_label(
    pause_menu_screen,
    text="GAME PAUSED",
    position=(-0.18, 0.28),
    scale=1.75,
    color_value=UI_TEXT,
    origin=(0, 0),
)
resume_button = create_framed_button(pause_menu_screen, ">  RESUME GAME", (-0.18, 0.13), (0.34, 0.07))
pause_settings_button = create_framed_button(pause_menu_screen, "*  SETTINGS", (-0.18, 0.04), (0.34, 0.07))
pause_save_button = create_framed_button(pause_menu_screen, "[S]  SAVE GAME", (-0.18, -0.05), (0.34, 0.07))
return_main_menu_button = create_framed_button(pause_menu_screen, "<  RETURN TO MAIN MENU", (-0.18, -0.14), (0.34, 0.07))
pause_quit_button = create_framed_button(pause_menu_screen, "X  QUIT GAME", (-0.18, -0.23), (0.34, 0.07))
pause_quit_button.frame.color = UI_DANGER
pause_controls_panel = create_panel(
    pause_menu_screen,
    position=(0.40, 0),
    scale=(0.44, 0.80),
)
pause_controls_title = create_label(
    pause_menu_screen,
    text="CONTROLS",
    position=(0.22, 0.28),
    scale=0.92,
    color_value=UI_SELECTED,
)
pause_controls_text = create_label(
    pause_menu_screen,
    text=(
        "WASD        Move\n"
        "Mouse       Look\n"
        "Space       Jump\n"
        "Shift       Sprint\n"
        "LMB / RMB   Break / Place\n"
        "E           Inventory\n"
        "Esc         Pause\n"
        "F5 / F9     Save / Load"
    ),
    position=(0.22, 0.20),
    scale=0.72,
    color_value=UI_MUTED_TEXT,
)

settings_screen = Entity(parent=camera.ui, enabled=False)
settings_backdrop = Entity(
    parent=settings_screen,
    model="quad",
    color=rgba255(0, 0, 0, 195),
    scale=(2, 1),
    z=0.20,
)
settings_panel = create_panel(
    settings_screen,
    position=(0, 0),
    scale=(1.36, 0.88),
)
settings_title = create_label(
    settings_screen,
    text="SETTINGS",
    position=(-0.62, 0.33),
    scale=1.55,
    color_value=UI_TEXT,
)
settings_tabs_panel = create_panel(
    settings_screen,
    position=(-0.54, -0.015),
    scale=(0.22, 0.58),
)
settings_general_tab = create_framed_button(settings_screen, "GENERAL", (-0.54, 0.18), (0.17, 0.06))
settings_video_tab = create_framed_button(settings_screen, "VIDEO", (-0.54, 0.09), (0.17, 0.06))
settings_controls_tab = create_framed_button(settings_screen, "CONTROLS", (-0.54, 0.0), (0.17, 0.06))
settings_about_tab = create_framed_button(settings_screen, "ABOUT", (-0.54, -0.09), (0.17, 0.06))
settings_general_tab.frame.color = UI_SELECTED
settings_category_hint = create_label(
    settings_screen,
    text="General settings are active.\nOther categories are visual guides\nfor future expansion.",
    position=(-0.62, -0.19),
    scale=0.53,
    color_value=UI_MUTED_TEXT,
)
settings_sensitivity_label = create_label(
    settings_screen,
    text="",
    position=(-0.40, 0.21),
    scale=0.72,
    color_value=UI_TEXT,
)
sensitivity_down_button = create_framed_button(settings_screen, "-", (-0.05, 0.21), (0.06, 0.055))
sensitivity_up_button = create_framed_button(settings_screen, "+", (0.03, 0.21), (0.06, 0.055))
settings_render_label = create_label(
    settings_screen,
    text="",
    position=(-0.40, 0.12),
    scale=0.72,
    color_value=UI_TEXT,
)
render_down_button = create_framed_button(settings_screen, "-", (-0.05, 0.12), (0.06, 0.055))
render_up_button = create_framed_button(settings_screen, "+", (0.03, 0.12), (0.06, 0.055))
settings_collider_label = create_label(settings_screen, "", (-0.40, 0.03), 0.72, UI_TEXT)
collider_down_button = create_framed_button(settings_screen, "-", (-0.05, 0.03), (0.06, 0.055))
collider_up_button = create_framed_button(settings_screen, "+", (0.03, 0.03), (0.06, 0.055))
fullscreen_label = create_label(settings_screen, "Fullscreen", (-0.40, -0.06), 0.72, UI_TEXT)
fullscreen_button = create_framed_button(settings_screen, "", (-0.01, -0.06), (0.14, 0.055))
debug_label = create_label(settings_screen, "Debug Text", (-0.40, -0.15), 0.72, UI_TEXT)
debug_button = create_framed_button(settings_screen, "", (-0.01, -0.15), (0.14, 0.055))
settings_budget_title = create_label(settings_screen, "CHUNK WORK BUDGETS", (0.15, 0.24), 0.72, UI_SELECTED)
settings_generation_budget_label = create_label(settings_screen, "", (0.15, 0.15), 0.68, UI_TEXT)
generation_budget_down_button = create_framed_button(settings_screen, "-", (0.52, 0.15), (0.06, 0.055))
generation_budget_up_button = create_framed_button(settings_screen, "+", (0.60, 0.15), (0.06, 0.055))
settings_rebuild_budget_label = create_label(settings_screen, "", (0.15, 0.06), 0.68, UI_TEXT)
rebuild_budget_down_button = create_framed_button(settings_screen, "-", (0.52, 0.06), (0.06, 0.055))
rebuild_budget_up_button = create_framed_button(settings_screen, "+", (0.60, 0.06), (0.06, 0.055))
settings_unload_budget_label = create_label(settings_screen, "", (0.15, -0.03), 0.68, UI_TEXT)
unload_budget_down_button = create_framed_button(settings_screen, "-", (0.52, -0.03), (0.06, 0.055))
unload_budget_up_button = create_framed_button(settings_screen, "+", (0.60, -0.03), (0.06, 0.055))
low_end_button = create_framed_button(settings_screen, "ENABLE LOW-END MODE", (0.37, -0.15), (0.43, 0.065))
settings_feedback_label = create_label(settings_screen, "", (0.15, -0.22), 0.60, UI_SELECTED)
settings_back_button = create_framed_button(settings_screen, "<  BACK", (0.37, -0.31), (0.28, 0.07))

multiplayer_screen = Entity(parent=camera.ui, enabled=False)
multiplayer_backdrop = Entity(
    parent=multiplayer_screen,
    model="quad",
    color=rgba255(0, 0, 0, 195),
    scale=(2, 1),
    z=0.20,
)
multiplayer_panel = create_panel(
    multiplayer_screen,
    position=(0, 0),
    scale=(0.68, 0.52),
)
multiplayer_title = create_label(
    multiplayer_screen,
    text="MULTIPLAYER",
    position=(0, 0.10),
    scale=1.8,
    color_value=UI_TEXT,
    origin=(0, 0),
)
multiplayer_message = create_label(
    multiplayer_screen,
    text="COMING SOON\nOnline play is planned for a future version.",
    position=(0, 0.01),
    scale=0.9,
    color_value=UI_MUTED_TEXT,
    origin=(0, 0),
)
multiplayer_back_button = create_menu_button(multiplayer_screen, "<  BACK", -0.15)


gameplay_hud_entities = [
    selected_text,
    status_text,
    help_text,
    health_label,
    hunger_label,
    survival_panel,
    hotbar_panel,
] + health_icons + hunger_icons + hotbar_slots + hotbar_texts + [
    slot.frame for slot in hotbar_slots
]


def is_gameplay_input_active():
    """Return whether first-person world interaction should run."""
    return game_state == "playing" and not inventory_open


def hide_menu_screens():
    """Hide all modal menu screens before showing the requested one."""
    main_menu_screen.enabled = False
    pause_menu_screen.enabled = False
    settings_screen.enabled = False
    multiplayer_screen.enabled = False


def sync_gameplay_input_state():
    """Synchronise mouse locking, HUD visibility, and world interaction cues."""
    gameplay_visible = game_state == "playing"
    interaction_active = is_gameplay_input_active()

    mouse.locked = interaction_active
    crosshair_horizontal.enabled = interaction_active
    crosshair_vertical.enabled = interaction_active
    coordinate_text.enabled = gameplay_visible and debug_text_enabled
    window.fps_counter.enabled = debug_text_enabled

    for entity in gameplay_hud_entities:
        entity.enabled = gameplay_visible

    if not interaction_active and "block_highlight" in globals():
        block_highlight.visible = False


def show_main_menu():
    """Show the launch menu and disable first-person controls."""
    global game_state

    if inventory_open:
        set_inventory_open(False)

    game_state = "main_menu"
    hide_menu_screens()
    main_menu_screen.enabled = True
    sync_gameplay_input_state()


def initialize_world_for_singleplayer():
    """Create or load world data only after Singleplayer is selected."""
    global last_player_chunk, world_initialized

    if world_initialized:
        return

    if os.path.exists(SAVE_FILE) and load_world():
        return

    generate_initial_world()
    player.position = find_safe_spawn()
    last_player_chunk = None
    schedule_chunks_around_player(force=True)
    activate_chunk(chunk_coord_from_block((player.x, 0, player.z)), immediate=True)
    world_initialized = True


def start_singleplayer():
    """Enter the generated or loaded world from the main menu."""
    global game_state

    initialize_world_for_singleplayer()
    game_state = "playing"
    hide_menu_screens()
    sync_gameplay_input_state()
    set_status("Singleplayer started. Press Esc to pause.")


def show_pause_menu():
    """Pause active gameplay and show in-game options."""
    global game_state

    if inventory_open:
        set_inventory_open(False)

    game_state = "paused"
    hide_menu_screens()
    pause_menu_screen.enabled = True
    sync_gameplay_input_state()


def resume_game():
    """Return from the pause menu to first-person gameplay."""
    global game_state

    game_state = "playing"
    hide_menu_screens()
    sync_gameplay_input_state()


def show_settings_menu(previous_menu=None):
    """Open settings and remember which menu should receive Back."""
    global game_state, settings_return_state

    settings_return_state = previous_menu or game_state
    game_state = "settings"
    hide_menu_screens()
    settings_screen.enabled = True
    update_settings_labels()
    sync_gameplay_input_state()


def return_from_settings():
    """Return to the menu that opened settings."""
    if settings_return_state == "paused":
        show_pause_menu()
    else:
        show_main_menu()


def show_multiplayer_notice():
    """Show an honest notice for the planned multiplayer feature."""
    global game_state

    game_state = "multiplayer_notice"
    hide_menu_screens()
    multiplayer_screen.enabled = True
    sync_gameplay_input_state()


def return_to_main_menu():
    """Leave gameplay controls disabled while preserving in-memory world data."""
    show_main_menu()


def save_from_pause_menu():
    """Save the current world without leaving the pause menu."""
    save_world()
    set_status("Game saved.")


def quit_game():
    """Cleanly close the application."""
    application.quit()


def update_settings_labels():
    """Refresh labels for settings that modify live game values."""
    debug_mode = "ON" if debug_text_enabled else "OFF"
    fullscreen_mode = "ON" if window.fullscreen else "OFF"
    settings_sensitivity_label.text = f"Mouse Sensitivity: {MOUSE_SENSITIVITY}"
    settings_render_label.text = f"Render Distance: {RENDER_DISTANCE} chunks"
    settings_collider_label.text = f"Collider Distance: {COLLIDER_DISTANCE} chunks"
    settings_generation_budget_label.text = f"Generate / frame: {MAX_CHUNK_GENERATIONS_PER_FRAME}"
    settings_rebuild_budget_label.text = f"Rebuild / frame: {MAX_CHUNK_REBUILDS_PER_FRAME}"
    settings_unload_budget_label.text = f"Unload / frame: {MAX_CHUNK_UNLOADS_PER_FRAME}"
    fullscreen_button.text = fullscreen_mode
    debug_button.text = debug_mode


def change_mouse_sensitivity(direction):
    """Adjust the live first-person mouse sensitivity."""
    global MOUSE_SENSITIVITY

    MOUSE_SENSITIVITY = max(
        MIN_MOUSE_SENSITIVITY,
        min(MAX_MOUSE_SENSITIVITY, MOUSE_SENSITIVITY + direction * MOUSE_SENSITIVITY_STEP),
    )
    player.mouse_sensitivity = Vec2(MOUSE_SENSITIVITY, MOUSE_SENSITIVITY)
    update_settings_labels()


def change_render_distance(direction):
    """Adjust render distance and refresh the streamed chunk target set."""
    global RENDER_DISTANCE, COLLIDER_DISTANCE, GENERATION_DISTANCE

    RENDER_DISTANCE = max(
        MIN_RENDER_DISTANCE,
        min(MAX_RENDER_DISTANCE, RENDER_DISTANCE + direction),
    )
    COLLIDER_DISTANCE = min(COLLIDER_DISTANCE, RENDER_DISTANCE)
    GENERATION_DISTANCE = RENDER_DISTANCE + 1
    if world_initialized:
        schedule_chunks_around_player(force=True)
    update_settings_labels()


def change_collider_distance(direction):
    """Adjust how many rendered chunks retain mesh colliders."""
    global COLLIDER_DISTANCE

    COLLIDER_DISTANCE = max(
        MIN_COLLIDER_DISTANCE,
        min(RENDER_DISTANCE, COLLIDER_DISTANCE + direction),
    )
    if world_initialized:
        schedule_chunks_around_player(force=True)
    update_settings_labels()


def change_chunk_budget(setting_name, direction):
    """Adjust one live per-frame chunk work limit within conservative bounds."""
    global MAX_CHUNK_GENERATIONS_PER_FRAME
    global MAX_CHUNK_REBUILDS_PER_FRAME
    global MAX_CHUNK_UNLOADS_PER_FRAME

    if setting_name == "generation":
        MAX_CHUNK_GENERATIONS_PER_FRAME = max(
            MIN_CHUNK_GENERATIONS_PER_FRAME,
            min(MAX_CHUNK_GENERATIONS_SETTING, MAX_CHUNK_GENERATIONS_PER_FRAME + direction),
        )
    elif setting_name == "rebuild":
        MAX_CHUNK_REBUILDS_PER_FRAME = max(
            MIN_CHUNK_REBUILDS_PER_FRAME,
            min(MAX_CHUNK_REBUILDS_SETTING, MAX_CHUNK_REBUILDS_PER_FRAME + direction),
        )
    elif setting_name == "unload":
        MAX_CHUNK_UNLOADS_PER_FRAME = max(
            MIN_CHUNK_UNLOADS_PER_FRAME,
            min(MAX_CHUNK_UNLOADS_SETTING, MAX_CHUNK_UNLOADS_PER_FRAME + direction),
        )

    update_settings_labels()


def enable_low_end_mode():
    """Apply a conservative preset for less powerful computers."""
    global RENDER_DISTANCE, COLLIDER_DISTANCE, GENERATION_DISTANCE
    global MAX_CHUNK_GENERATIONS_PER_FRAME
    global MAX_CHUNK_REBUILDS_PER_FRAME
    global MAX_CHUNK_UNLOADS_PER_FRAME
    global debug_text_enabled

    RENDER_DISTANCE = 1
    COLLIDER_DISTANCE = 1
    GENERATION_DISTANCE = RENDER_DISTANCE + 1
    MAX_CHUNK_GENERATIONS_PER_FRAME = 1
    MAX_CHUNK_REBUILDS_PER_FRAME = 1
    MAX_CHUNK_UNLOADS_PER_FRAME = 2
    debug_text_enabled = False
    settings_feedback_label.text = "Low-End Mode enabled."

    if world_initialized:
        schedule_chunks_around_player(force=True)

    update_settings_labels()
    sync_gameplay_input_state()
    set_status("Low-End Mode enabled.")


def toggle_fullscreen():
    """Switch between fullscreen and windowed display modes."""
    window.fullscreen = not window.fullscreen
    update_settings_labels()


def toggle_debug_text():
    """Toggle FPS and coordinate diagnostics."""
    global debug_text_enabled

    debug_text_enabled = not debug_text_enabled
    update_settings_labels()
    sync_gameplay_input_state()


singleplayer_button.on_click = start_singleplayer
multiplayer_button.on_click = show_multiplayer_notice
main_settings_button.on_click = Func(show_settings_menu, "main_menu")
main_quit_button.on_click = quit_game
resume_button.on_click = resume_game
pause_settings_button.on_click = Func(show_settings_menu, "paused")
pause_save_button.on_click = save_from_pause_menu
return_main_menu_button.on_click = return_to_main_menu
pause_quit_button.on_click = quit_game
sensitivity_down_button.on_click = Func(change_mouse_sensitivity, -1)
sensitivity_up_button.on_click = Func(change_mouse_sensitivity, 1)
render_down_button.on_click = Func(change_render_distance, -1)
render_up_button.on_click = Func(change_render_distance, 1)
collider_down_button.on_click = Func(change_collider_distance, -1)
collider_up_button.on_click = Func(change_collider_distance, 1)
generation_budget_down_button.on_click = Func(change_chunk_budget, "generation", -1)
generation_budget_up_button.on_click = Func(change_chunk_budget, "generation", 1)
rebuild_budget_down_button.on_click = Func(change_chunk_budget, "rebuild", -1)
rebuild_budget_up_button.on_click = Func(change_chunk_budget, "rebuild", 1)
unload_budget_down_button.on_click = Func(change_chunk_budget, "unload", -1)
unload_budget_up_button.on_click = Func(change_chunk_budget, "unload", 1)
low_end_button.on_click = enable_low_end_mode
fullscreen_button.on_click = toggle_fullscreen
debug_button.on_click = toggle_debug_text
settings_back_button.on_click = return_from_settings
multiplayer_back_button.on_click = show_main_menu


def set_inventory_open(is_open):
    """Show or hide the inventory and update mouse/controller state."""
    global inventory_open

    if is_open and game_state != "playing":
        return

    if inventory_open and not is_open:
        return_crafting_items()

    inventory_open = is_open
    inventory_screen.enabled = is_open
    sync_gameplay_input_state()
    update_ui()


def toggle_inventory():
    """Toggle the inventory overlay."""
    set_inventory_open(not inventory_open)


def set_status(message, duration=3.0):
    """Show a temporary message in the top-left UI."""
    global status_message_timer
    status_text.text = message
    status_message_timer = duration


def update_ui():
    """Refresh hotbar, inventory, crafting, health, and hunger UI."""
    current_block = BLOCK_ORDER[selected_index]
    selected_text.text = f"Selected: {current_block.title()} x{inventory.get(current_block, 0)}"
    active_collider_chunks = sum(
        1
        for chunk_coord, collider_enabled in chunk_collider_states.items()
        if collider_enabled and chunk_coord in chunks and chunks[chunk_coord]
    )
    coordinate_text.text = (
        f"XYZ: {int(player.x)}, {int(player.y)}, {int(player.z)}\n"
        f"Chunks: {len(chunks)} rendered | {active_collider_chunks} colliders\n"
        f"Queued: {len(chunk_generation_queue)} generation | {len(dirty_chunks)} rebuilds\n"
        f"Distance: {RENDER_DISTANCE} render | {COLLIDER_DISTANCE} collider"
    )

    filled_health_icons = int(math.ceil(max(0.0, min(100.0, health)) / 10))
    filled_hunger_icons = int(math.ceil(max(0.0, min(100.0, hunger)) / 10))
    for i in range(10):
        set_icon_color(health_icons[i], UI_DANGER if i < filled_health_icons else UI_DIM)
        set_icon_color(
            hunger_icons[i],
            rgba255(218, 150, 58, 255)
            if i < filled_hunger_icons
            else UI_DIM,
        )

    for i, block_type in enumerate(BLOCK_ORDER):
        count = inventory.get(block_type, 0)
        hotbar_texts[i].text = f"{i + 1}\n{block_type[:3]}\n{count}"
        inventory_slots[i].text = f"{block_type.title()}\n{count}"
        inventory_hotbar_slots[i].text = f"{i + 1}\n{block_type[:3]}\n{count}"

        if i == selected_index:
            hotbar_slots[i].frame.color = UI_SELECTED
            inventory_slots[i].frame.color = UI_SELECTED
            inventory_hotbar_slots[i].frame.color = UI_SELECTED
        else:
            hotbar_slots[i].frame.color = UI_PANEL_BORDER
            inventory_slots[i].frame.color = UI_PANEL_BORDER
            inventory_hotbar_slots[i].frame.color = UI_PANEL_BORDER

    for i, block_type in enumerate(crafting_grid):
        crafting_slots[i].text = block_type.title() if block_type else "Empty"
        crafting_slots[i].color = (
            UI_BLUE
            if block_type
            else UI_SLOT
        )

    held_item_text.text = (
        f"Held item: {held_crafting_item.title()}"
        if held_crafting_item
        else "Held item: none"
    )

    recipe = get_matching_recipe()
    if recipe is None:
        crafting_output_slot.text = "Output\n-"
        crafting_output_slot.color = UI_SLOT
        crafting_output_slot.frame.color = UI_PANEL_BORDER
    else:
        result_item, result_amount = recipe["result"]
        crafting_output_slot.text = f"Output\n{result_item.title()} x{result_amount}"
        crafting_output_slot.color = rgba255(95, 135, 82, 255)
        crafting_output_slot.frame.color = UI_SELECTED


# ------------------------------------------------------------
# Building and mining
# ------------------------------------------------------------

def block_coord_from_hit(hit, place_against_face=False):
    """Convert a shared chunk-mesh hit into the adjacent block coordinate."""
    direction = 0.01 if place_against_face else -0.01
    point = hit.world_point + hit.normal * direction

    return (
        int(math.floor(point.x + 0.5)),
        int(math.floor(point.y + 0.5)),
        int(math.floor(point.z + 0.5)),
    )


def raycast_chunk_mesh():
    """Raycast the rendered chunk meshes used for voxel interaction."""
    hit = raycast(
        camera.world_position,
        camera.forward,
        distance=REACH_DISTANCE,
        ignore=[player],
    )

    if not hit.hit or not getattr(hit.entity, "is_chunk_mesh", False):
        return None

    return hit


def update_block_highlight():
    """Move one reusable outline cube onto the block under the crosshair."""
    global highlighted_block_coord

    if not is_gameplay_input_active():
        highlighted_block_coord = None
        block_highlight.visible = False
        return

    hit = raycast_chunk_mesh()
    if hit is None:
        highlighted_block_coord = None
        block_highlight.visible = False
        return

    coord = block_coord_from_hit(hit)
    if coord not in world_data:
        highlighted_block_coord = None
        block_highlight.visible = False
        return

    highlighted_block_coord = coord
    block_highlight.position = coord
    block_highlight.visible = True


def break_block():
    """Break the block currently looked at."""
    hit = raycast_chunk_mesh()

    if hit is None:
        return

    coord = block_coord_from_hit(hit)
    block_type = world_data.get(coord)

    if block_type is not None and remove_block(coord):
        inventory[block_type] = inventory.get(block_type, 0) + 1
        set_status(f"Broke {block_type}.")
        update_ui()


def place_block():
    """Place the selected block against the block currently looked at."""
    current_block = BLOCK_ORDER[selected_index]

    if inventory.get(current_block, 0) <= 0:
        set_status(f"No {current_block} left.")
        return

    hit = raycast_chunk_mesh()

    if hit is None:
        return

    coord = block_coord_from_hit(hit, place_against_face=True)

    # Do not place inside the player's body.
    inside_player_x = abs(coord[0] - player.x) < 0.8
    inside_player_y = player.y - 1.0 < coord[1] < player.y + 1.8
    inside_player_z = abs(coord[2] - player.z) < 0.8

    if inside_player_x and inside_player_y and inside_player_z:
        set_status("Can't place inside yourself.")
        return

    if coord in world_data:
        return

    if add_block(coord, current_block, create_entity=True):
        inventory[current_block] -= 1
        set_status(f"Placed {current_block}.")
        update_ui()


# ------------------------------------------------------------
# Input handling
# ------------------------------------------------------------

def input(key):
    """Handle keyboard and mouse input."""
    global selected_index

    if key == "escape":
        if inventory_open:
            set_inventory_open(False)
            return

        if game_state == "playing":
            show_pause_menu()
        elif game_state == "paused":
            resume_game()
        elif game_state == "settings":
            return_from_settings()
        elif game_state == "multiplayer_notice":
            show_main_menu()
        return

    if game_state != "playing":
        return

    if key == "e":
        toggle_inventory()
        return

    if key in ["1", "2", "3", "4", "5", "6", "7", "8"]:
        selected_index = int(key) - 1
        update_ui()

    if inventory_open:
        return

    if key == "left mouse down":
        break_block()

    if key == "right mouse down":
        place_block()

    if key == "f5":
        save_world()

    if key == "f9":
        load_world()


# ------------------------------------------------------------
# Game loop
# ------------------------------------------------------------

block_highlight = Entity(
    model="cube",
    color=rgba255(255, 235, 90, 180),
    scale=1.025,
    wireframe=True,
    collider=None,
    visible=False,
)


def update_day_night():
    """Simple day/night cycle using sky and light color."""
    global day_timer

    day_timer += time.dt
    angle = (day_timer / DAY_LENGTH_SECONDS) * math.tau

    # daylight ranges from about 0 at night to 1 at noon.
    daylight = (math.sin(angle - math.pi / 2) + 1) / 2
    daylight = max(0.08, daylight)

    sky_color = lerp(
        rgb255(10, 14, 35),
        rgb255(135, 206, 235),
        daylight,
    )

    window.color = sky_color
    sky.color = sky_color

    sun.rotation_x = 180 - math.degrees(angle)
    sun.color = lerp(
        rgb255(60, 70, 120),
        rgb255(255, 245, 220),
        daylight,
    )

    ambient.color = lerp(
        rgba255(35, 40, 70, 255),
        rgba255(130, 130, 130, 255),
        daylight,
    )


def update_survival_stats():
    """Update hunger and health over time."""
    global health, hunger

    # Sprinting makes hunger fall a little faster.
    hunger_loss = 0.45 if held_keys["left shift"] else 0.20
    hunger = max(0.0, hunger - hunger_loss * time.dt)

    # Starve slowly if hunger is empty.
    if hunger <= 0:
        health = max(0.0, health - 1.2 * time.dt)

    # Very slow regeneration when well-fed.
    if hunger > 75 and health < 100:
        health = min(100.0, health + 0.25 * time.dt)

    if player.y < -20:
        health = 0

    if health <= 0:
        set_status("You died! Respawning...")
        health = 100.0
        hunger = 100.0
        player.position = find_safe_spawn()


def update_status_message():
    """Hide status text after a few seconds."""
    global status_message_timer

    if status_message_timer > 0:
        status_message_timer -= time.dt
        if status_message_timer <= 0:
            status_text.text = ""


def resolve_player_ceiling_collision():
    """Stop jump animation when the player's head reaches an overhead block."""
    hit = raycast(
        player.world_position + Vec3(0, 0.05, 0),
        Vec3(0, 1, 0),
        distance=player.height + CEILING_COLLISION_MARGIN + 0.05,
        traverse_target=player.traverse_target,
        ignore=player.ignore_list,
    )

    if (
        not hit.hit
        or not getattr(hit.entity, "is_chunk_mesh", False)
        or hit.world_normal.y > -0.7
    ):
        return

    max_player_y = hit.world_point.y - player.height - CEILING_COLLISION_MARGIN
    if player.y < max_player_y:
        return

    player.y = max_player_y
    if hasattr(player, "y_animator"):
        player.y_animator.pause()

    player.jumping = False
    player.grounded = False
    player.air_time = max(player.air_time, 0.05)


def update():
    """Main update loop called every frame."""
    global chunk_stream_update_timer, ui_update_timer

    update_block_highlight()
    update_day_night()
    update_status_message()

    if game_state == "playing":
        player.speed = SPRINT_SPEED if held_keys["left shift"] else NORMAL_SPEED
        resolve_player_ceiling_collision()
        update_survival_stats()

        chunk_stream_update_timer -= time.dt
        if chunk_stream_update_timer <= 0:
            schedule_chunks_around_player()
            chunk_stream_update_timer = CHUNK_STREAM_UPDATE_SECONDS

    process_chunk_streaming()
    rebuild_dirty_chunks()

    ui_update_timer -= time.dt
    if ui_update_timer <= 0:
        update_ui()
        ui_update_timer = UI_REFRESH_SECONDS


# ------------------------------------------------------------
# Start game
# ------------------------------------------------------------

update_ui()
update_settings_labels()

show_main_menu()
app.run()
