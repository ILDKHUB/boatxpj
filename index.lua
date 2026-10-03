--[[
    R6 Pose Animator (Fixed build)
    Client-side editor with an isolated preview rig.

Export:
        JSON             Project data.
        LuaAnimationLib  ModuleScript with Sample / Play.
        Lua             Remote playback script.

Clipboard:
        Uses setclipboard / toclipboard when available.
        Otherwise opens a selectable TextBox.

Remote assumptions:
        ChangeOffsetForPart(partName, Vector3)
        ChangeTransformationForPart(partName, rotationCFrame)

FIXES IN THIS BUILD:
        * Remote axis fix: the pose remotes expect offsets with X/Y
          swapped and Z inverted. All values sent to the server are
          remapped (position AND rotation) so what you see in the
          preview matches what the server applies.
          Toggle with CONFIG.REMOTE_AXIS_FIX if your server differs.
        * Mobile camera lock: starting any drag (gizmo, Drag Axis,
          timeline scrub, window move) on a touch screen now locks the
          camera so the view no longer rotates while you drag.

Preview is based on the rig's Motor6D bind pose at rebuild time.
    If your server applies different transform semantics,
    adapt sendPose() and renderPreview().
]]

local CONFIG = {
    REMOTE_HZ = 20, -- 0 = check/send changed values every Heartbeat
    MAX_DURATION = 300,
    HISTORY_LIMIT = 60,
    PREVIEW_OFFSET = Vector3.new(5, 0, 0),
    DEFAULT_DURATION = 5,
    DEFAULT_ZOOM = 100,
    MOVE_STEP = 0.1,
    ROTATE_STEP = 5,
    MOBILE_MOVE_PER_PIXEL = 0.025,
    MOBILE_ROTATE_PER_PIXEL = 0.5,
    REMOTE_AXIS_FIX = true, -- swap X/Y and invert Z for pose remotes
}

local Players = game:GetService("Players")
local RunService = game:GetService("RunService")
local TweenService = game:GetService("TweenService")
local UserInputService = game:GetService("UserInputService")
local HttpService = game:GetService("HttpService")

local player = Players.LocalPlayer
assert(player, "Run this script on the client.")

local playerGui = player:WaitForChild("PlayerGui")

local environment = _G
if type(getgenv) == "function" then
    environment = getgenv()
end

local SESSION_KEY = "__R6_POSE_ANIMATOR_SESSION"
local CAMERA_RESTORE_KEY = "__R6_POSE_ANIMATOR_CAMERA_RESTORE"

-- Restore a camera left locked by a previous session.
do
    local leftover = environment[CAMERA_RESTORE_KEY]
    local camera = workspace.CurrentCamera
    if leftover and camera and camera.CameraType == Enum.CameraType.Scriptable then
        camera.CameraType = leftover
    end
    environment[CAMERA_RESTORE_KEY] = nil
end

if type(environment[SESSION_KEY]) == "function" then
    pcall(environment[SESSION_KEY])
end

local PARTS = {
    "Head",
    "Torso",
    "Right Arm",
    "Left Arm",
    "Right Leg",
    "Left Leg",
}

local COLORS = {
    Window = Color3.fromRGB(23, 25, 30),
    Panel = Color3.fromRGB(31, 34, 41),
    Field = Color3.fromRGB(40, 44, 53),
    Border = Color3.fromRGB(61, 66, 78),
    Text = Color3.fromRGB(227, 231, 239),
    Muted = Color3.fromRGB(156, 164, 181),
    Accent = Color3.fromRGB(95, 157, 255),
    Selected = Color3.fromRGB(49, 68, 98),
    Key = Color3.fromRGB(241, 181, 81),
    X = Color3.fromRGB(231, 97, 97),
    Y = Color3.fromRGB(102, 211, 132),
    Z = Color3.fromRGB(105, 153, 238),
}

local connections = {}
local alive = true
local dragging = nil
local ghost = nil
local previewParts = {}
local joints = {}
local jointByPart = {}
local previewBases = {}
local previewOrigin = CFrame.identity

local project = {
    format = "R6PoseAnimator",
    version = 1,
    rig = "R6",
    duration = CONFIG.DEFAULT_DURATION,
    fps = 30,
    tracks = {},
}

for _, name in ipairs(PARTS) do
    project.tracks[name] = {}
end

local selectedPart = "Head"
local selectedAxis = "X"
local mode = "Move"
local currentTime = 0
local speed = 1
local looping = true
local playing = false
local live = false
local snapping = true
local zoom = CONFIG.DEFAULT_ZOOM

local undoStack = {}
local redoStack = {}
local remoteCache = {}
local remoteAccumulator = 0
local remotes = {}
local resetArmedUntil = 0

local refreshTimeline
local refreshInspector
local refreshButtons
local buildPreview
local exportProject
local cleanup

-- Remote axis correction ------------------------------------------------------
-- The remotes apply offsets in a basis whose X/Y are swapped relative to the
-- preview basis and whose Z is inverted. For a pure rotation M (M = M^-1 here)
-- the consistent fix is:  position' = M * position   and   rotation' = M * R
local AXIS_FIX = CFrame.new(0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1)

local function fixPositionForRemote(position)
    if not CONFIG.REMOTE_AXIS_FIX then
        return position
    end
    return AXIS_FIX * position
end

local function fixRotationForRemote(rotation)
    if not CONFIG.REMOTE_AXIS_FIX then
        return rotation
    end
    return AXIS_FIX * rotation
end

-- Camera lock while dragging (mobile) ------------------------------------------
local cameraLockCount = 0
local savedCameraType = nil

local function lockCamera()
    cameraLockCount += 1
    if cameraLockCount == 1 then
        local camera = workspace.CurrentCamera
        if camera and camera.CameraType ~= Enum.CameraType.Scriptable then
            savedCameraType = camera.CameraType
            environment[CAMERA_RESTORE_KEY] = savedCameraType
            camera.CameraType = Enum.CameraType.Scriptable
        end
    end
end

local function unlockCamera()
    if cameraLockCount <= 0 then
        return
    end
    cameraLockCount -= 1
    if cameraLockCount == 0 and savedCameraType then
        local camera = workspace.CurrentCamera
        if camera and camera.CameraType == Enum.CameraType.Scriptable then
            camera.CameraType = savedCameraType
        end
        savedCameraType = nil
        environment[CAMERA_RESTORE_KEY] = nil
    end
end

local function connect(signal, callback)
    local connection = signal:Connect(callback)
    connections[#connections + 1] = connection
    return connection
end

local function make(className, properties, parent)
    local object = Instance.new(className)

    for key, value in pairs(properties or {}) do
        object[key] = value
    end

    object.Parent = parent
    return object
end

local function corner(object, radius)
    make("UICorner", {
        CornerRadius = UDim.new(0, radius or 4),
    }, object)
end

local function deepCopy(value)
    if type(value) ~= "table" then
        return value
    end

    local result = {}

    for key, item in pairs(value) do
        result[key] = deepCopy(item)
    end

    return result
end

local function finiteNumber(text)
    local value = tonumber(text)

    if not value or value ~= value or math.abs(value) == math.huge then
        return nil
    end

    return value
end

local function round(value, step)
    return math.round(value / step) * step
end

local function editTime(value)
    value = math.clamp(value, 0, project.duration)

    if snapping then
        value = round(value, 1 / project.fps)
    end

    return math.clamp(value, 0, project.duration)
end

local function rotationFromArray(array)
    return CFrame.Angles(
        math.rad(array[1]),
        math.rad(array[2]),
        math.rad(array[3])
    )
end

local function rotationToArray(rotation)
    local x, y, z = rotation:ToEulerAnglesXYZ()

    return {
        math.deg(x),
        math.deg(y),
        math.deg(z),
    }
end

local function poseFromKey(key)
    return {
        position = Vector3.new(key.p[1], key.p[2], key.p[3]),
        rotation = rotationFromArray(key.r),
    }
end

local function evaluateTrack(track, time)
    if #track == 0 then
        return {
            position = Vector3.zero,
            rotation = CFrame.identity,
        }
    end

    if time <= track[1].t then
        return poseFromKey(track[1])
    end

    if time >= track[#track].t then
        return poseFromKey(track[#track])
    end

    for index = 1, #track - 1 do
        local first = track[index]
        local second = track[index + 1]

        if time >= first.t and time <= second.t then
            local alpha = (time - first.t) / (second.t - first.t)

            alpha = TweenService:GetValue(
                alpha,
                Enum.EasingStyle[first.e or "Linear"],
                Enum.EasingDirection[first.d or "InOut"]
            )

            local a = poseFromKey(first)
            local b = poseFromKey(second)

            return {
                position = a.position:Lerp(b.position, alpha),
                rotation = a.rotation:Lerp(b.rotation, alpha),
            }
        end
    end

    return poseFromKey(track[#track])
end

local function evaluate(time)
    local result = {}

    for _, name in ipairs(PARTS) do
        result[name] = evaluateTrack(project.tracks[name], time)
    end

    return result
end

local function findKey(name, time)
    for index, key in ipairs(project.tracks[name]) do
        if math.abs(key.t - time) < 0.0001 then
            return key, index
        end
    end

    return nil
end

local function sortTrack(name)
    table.sort(project.tracks[name], function(a, b)
        return a.t < b.t
    end)
end

local function ensureKey(name)
    local existing = findKey(name, currentTime)

    if existing then
        return existing
    end

    local pose = evaluateTrack(project.tracks[name], currentTime)

    local key = {
        t = currentTime,
        p = {
            pose.position.X,
            pose.position.Y,
            pose.position.Z,
        },
        r = rotationToArray(pose.rotation),
        e = "Linear",
        d = "InOut",
    }

    table.insert(project.tracks[name], key)
    sortTrack(name)

    return key
end

local function pushUndo()
    table.insert(undoStack, deepCopy(project))

    if #undoStack > CONFIG.HISTORY_LIMIT then
        table.remove(undoStack, 1)
    end

    table.clear(redoStack)
end

local function prepareEdit()
    playing = false
    currentTime = editTime(currentTime)
    pushUndo()

    if refreshButtons then
        refreshButtons()
    end
end

local function finishEdit()
    refreshTimeline()
    refreshInspector()
    refreshButtons()
end

local function setPoseKey(key, position, rotation)
    key.p = { position.X, position.Y, position.Z }
    key.r = rotationToArray(rotation)
end

-- GUI ------------------------------------------------------------------------

local gui = make("ScreenGui", {
    Name = "R6PoseAnimator",
    ResetOnSpawn = false,
    IgnoreGuiInset = true,
    ZIndexBehavior = Enum.ZIndexBehavior.Sibling,
    DisplayOrder = 80,
}, playerGui)

local window = make("Frame", {
    Name = "Window",
    BackgroundColor3 = COLORS.Window,
    BorderSizePixel = 0,
    ClipsDescendants = true,
    Active = true,
}, gui)
corner(window, 7)

make("UIStroke", {
    Color = COLORS.Border,
    Thickness = 1,
}, window)

local titleBar = make("Frame", {
    Size = UDim2.new(1, 0, 0, 30),
    BackgroundColor3 = COLORS.Panel,
    BorderSizePixel = 0,
    Active = true,
}, window)

local title = make("TextLabel", {
    Position = UDim2.fromOffset(10, 0),
    Size = UDim2.new(1, -90, 1, 0),
    BackgroundTransparency = 1,
    Text = "R6 Pose Animator",
    TextColor3 = COLORS.Text,
    TextSize = 14,
    Font = Enum.Font.GothamMedium,
    TextXAlignment = Enum.TextXAlignment.Left,
}, titleBar)

local function button(parent, text, width)
    local object = make("TextButton", {
        Size = UDim2.fromOffset(width or 75, 26),
        BackgroundColor3 = COLORS.Field,
        BorderSizePixel = 0,
        Text = text,
        TextSize = 11,
        TextColor3 = COLORS.Text,
        Font = Enum.Font.GothamMedium,
        AutoButtonColor = true,
    }, parent)
    corner(object, 4)
    return object
end

local closeButton = button(titleBar, "Close", 56)
closeButton.Position = UDim2.new(1, -62, 0, 2)

local function horizontalBar(y, height)
    local frame = make("ScrollingFrame", {
        Position = UDim2.fromOffset(6, y),
        Size = UDim2.new(1, -12, 0, height),
        BackgroundTransparency = 1,
        BorderSizePixel = 0,
        ScrollBarThickness = 3,
        ScrollingDirection = Enum.ScrollingDirection.X,
        AutomaticCanvasSize = Enum.AutomaticSize.X,
        CanvasSize = UDim2.fromOffset(0, 0),
        ElasticBehavior = Enum.ElasticBehavior.Never,
    }, window)

    make("UIListLayout", {
        FillDirection = Enum.FillDirection.Horizontal,
        Padding = UDim.new(0, 5),
        SortOrder = Enum.SortOrder.LayoutOrder,
        VerticalAlignment = Enum.VerticalAlignment.Top,
    }, frame)

    return frame
end

local toolbar = horizontalBar(36, 32)
local tools = horizontalBar(71, 32)
local settings = horizontalBar(106, 34)
local inspector = horizontalBar(143, 46)

local playButton = button(toolbar, "Play", 57)
local stopButton = button(toolbar, "Stop", 57)
local loopButton = button(toolbar, "Loop: On", 76)
local liveButton = button(toolbar, "Live: Off", 76)
local addButton = button(toolbar, "Add Key", 72)
local addAllButton = button(toolbar, "Key All", 70)
local deleteButton = button(toolbar, "Delete Key", 83)
local undoButton = button(toolbar, "Undo", 58)
local redoButton = button(toolbar, "Redo", 58)
local resetButton = button(toolbar, "Reset", 67)

local moveButton = button(tools, "Move", 62)
local rotateButton = button(tools, "Rotate", 66)
local axisButtons = {}

for _, axis in ipairs({ "X", "Y", "Z" }) do
    axisButtons[axis] = button(tools, axis, 32)
end

local axisPad = button(tools, "Drag Axis", 110)
axisPad.AutoButtonColor = false

local rigButton = button(tools, "Set R6", 65)
local rebuildButton = button(tools, "Rebuild Preview", 112)
local resetRemoteButton = button(tools, "Reset Remote", 103)
local jsonButton = button(tools, "JSON", 56)
local libraryButton = button(tools, "LuaAnimationLib", 124)
local luaButton = button(tools, "Lua", 48)

local function field(parent, caption, initial, width, height)
    width = width or 78
    height = height or 31

    local holder = make("Frame", {
        Size = UDim2.fromOffset(width, height),
        BackgroundTransparency = 1,
    }, parent)

    make("TextLabel", {
        Size = UDim2.new(1, 0, 0, 12),
        BackgroundTransparency = 1,
        Text = caption,
        TextColor3 = COLORS.Muted,
        Font = Enum.Font.Gotham,
        TextSize = 10,
        TextXAlignment = Enum.TextXAlignment.Left,
    }, holder)

    local box = make("TextBox", {
        Position = UDim2.fromOffset(0, 13),
        Size = UDim2.new(1, 0, 1, -13),
        BackgroundColor3 = COLORS.Field,
        BorderSizePixel = 0,
        Text = initial,
        TextColor3 = COLORS.Text,
        TextSize = 11,
        Font = Enum.Font.Code,
        ClearTextOnFocus = false,
    }, holder)
    corner(box, 3)

    return box
end

local timeBox = field(settings, "Time", "0", 66)
local durationBox = field(settings, "Duration", tostring(project.duration), 70)
local speedBox = field(settings, "Speed", "1", 58)
local fpsBox = field(settings, "FPS", "30", 48)
local zoomBox = field(settings, "Zoom", tostring(zoom), 58)
local moveStepBox = field(settings, "Move Step", tostring(CONFIG.MOVE_STEP), 72)
local rotateStepBox = field(settings, "Rotate Step", tostring(CONFIG.ROTATE_STEP), 76)
local snapButton = button(settings, "Snap: On", 76)

local inspectorTitle = make("TextLabel", {
    Size = UDim2.fromOffset(88, 42),
    BackgroundTransparency = 1,
    Text = selectedPart,
    TextColor3 = COLORS.Text,
    Font = Enum.Font.GothamMedium,
    TextSize = 11,
    TextWrapped = true,
}, inspector)

local poseFields = {}

for _, name in ipairs({ "PX", "PY", "PZ", "RX", "RY", "RZ" }) do
    poseFields[name] = field(inspector, name, "0", 62, 42)
end

local easingButton = button(inspector, "Linear", 100)
local directionButton = button(inspector, "InOut", 68)

local timelineArea = make("Frame", {
    Position = UDim2.fromOffset(6, 196),
    Size = UDim2.new(1, -12, 1, -222),
    BackgroundColor3 = COLORS.Panel,
    BorderSizePixel = 0,
    ClipsDescendants = true,
}, window)
corner(timelineArea, 4)

local namesPanel = make("Frame", {
    Size = UDim2.new(0, 100, 1, 0),
    BackgroundColor3 = COLORS.Panel,
    BorderSizePixel = 0,
    ClipsDescendants = true,
}, timelineArea)

local namesContent = make("Frame", {
    Size = UDim2.fromOffset(100, 210),
    BackgroundTransparency = 1,
}, namesPanel)

local timeline = make("ScrollingFrame", {
    Position = UDim2.fromOffset(102, 0),
    Size = UDim2.new(1, -102, 1, 0),
    BackgroundTransparency = 1,
    BorderSizePixel = 0,
    ScrollBarThickness = 7,
    ScrollBarImageColor3 = COLORS.Muted,
    ScrollingDirection = Enum.ScrollingDirection.XY,
    CanvasSize = UDim2.fromOffset(600, 210),
    ElasticBehavior = Enum.ElasticBehavior.Never,
}, timelineArea)

local timelineContent = make("Frame", {
    BackgroundTransparency = 1,
    Size = UDim2.fromOffset(600, 210),
}, timeline)

local statusLabel = make("TextLabel", {
    Position = UDim2.new(0, 9, 1, -23),
    Size = UDim2.new(1, -18, 0, 20),
    BackgroundTransparency = 1,
    Text = "Local preview. Live is off.",
    TextColor3 = COLORS.Muted,
    Font = Enum.Font.Gotham,
    TextSize = 10,
    TextXAlignment = Enum.TextXAlignment.Left,
    TextTruncate = Enum.TextTruncate.AtEnd,
}, window)

local function status(text)
    if alive then
        statusLabel.Text = text
    end
end

local outputPanel = make("Frame", {
    Position = UDim2.fromScale(0.05, 0.05),
    Size = UDim2.fromScale(0.9, 0.9),
    BackgroundColor3 = COLORS.Window,
    BorderSizePixel = 0,
    Visible = false,
    ZIndex = 30,
}, gui)
corner(outputPanel, 6)

local outputTitle = make("TextLabel", {
    Position = UDim2.fromOffset(10, 0),
    Size = UDim2.new(1, -95, 0, 34),
    BackgroundTransparency = 1,
    Text = "Export",
    TextColor3 = COLORS.Text,
    TextSize = 13,
    Font = Enum.Font.GothamMedium,
    TextXAlignment = Enum.TextXAlignment.Left,
    ZIndex = 31,
}, outputPanel)

local outputClose = button(outputPanel, "Close", 60)
outputClose.Position = UDim2.new(1, -70, 0, 4)
outputClose.ZIndex = 31

local outputScroll = make("ScrollingFrame", {
    Position = UDim2.fromOffset(8, 38),
    Size = UDim2.new(1, -16, 1, -46),
    BackgroundColor3 = COLORS.Panel,
    BorderSizePixel = 0,
    ScrollBarThickness = 7,
    AutomaticCanvasSize = Enum.AutomaticSize.Y,
    CanvasSize = UDim2.fromOffset(0, 0),
    ZIndex = 31,
}, outputPanel)

local outputBox = make("TextBox", {
    Size = UDim2.new(1, -12, 0, 200),
    AutomaticSize = Enum.AutomaticSize.Y,
    BackgroundTransparency = 1,
    ClearTextOnFocus = false,
    MultiLine = true,
    TextEditable = true,
    TextWrapped = true,
    Text = "",
    TextColor3 = COLORS.Text,
    TextSize = 12,
    Font = Enum.Font.Code,
    TextXAlignment = Enum.TextXAlignment.Left,
    TextYAlignment = Enum.TextYAlignment.Top,
    ZIndex = 32,
}, outputScroll)

connect(outputClose.Activated, function()
    outputPanel.Visible = false
end)

-- Window placement and generic pointer dragging -------------------------------

local windowPlaced = false

local function fitWindow()
    local camera = workspace.CurrentCamera
    if not camera then
        return
    end

    local viewport = camera.ViewportSize
    local width = math.max(240, math.min(1080, viewport.X - 16))
    local height = math.min(
        viewport.Y - 16,
        math.clamp(viewport.Y * 0.6, 290, 460)
    )

    window.Size = UDim2.fromOffset(width, height)

    if not windowPlaced then
        window.Position = UDim2.fromOffset(
            math.max(0, (viewport.X - width) / 2),
            math.max(0, viewport.Y - height - 8)
        )
        windowPlaced = true
    else
        window.Position = UDim2.fromOffset(
            math.clamp(window.Position.X.Offset, 0, math.max(0, viewport.X - width)),
            math.clamp(window.Position.Y.Offset, 0, math.max(0, viewport.Y - height))
        )
    end
end

fitWindow()

local observedCamera

local function observeCamera()
    if observedCamera then
        observedCamera:Disconnect()
        observedCamera = nil
    end

    local camera = workspace.CurrentCamera

    if camera then
        observedCamera = connect(
            camera:GetPropertyChangedSignal("ViewportSize"),
            fitWindow
        )
    end

    fitWindow()
end

connect(workspace:GetPropertyChangedSignal("CurrentCamera"), observeCamera)
observeCamera()

local function isPointer(input)
    return input.UserInputType == Enum.UserInputType.MouseButton1
        or input.UserInputType == Enum.UserInputType.Touch
end

local function beginDrag(input, onMove, onEnd)
    if dragging then
        return false
    end

    dragging = {
        input = input,
        move = onMove,
        finish = onEnd,
    }

    -- Lock the camera for touch drags so the view cannot rotate
    -- while the user is dragging on a phone/tablet.
    if input.UserInputType == Enum.UserInputType.Touch then
        lockCamera()
    end

    return true
end

connect(UserInputService.InputChanged, function(input)
    local active = dragging
    if not active then
        return
    end

    local sameTouch = input == active.input
    local mouseMove =
        active.input.UserInputType == Enum.UserInputType.MouseButton1
        and input.UserInputType == Enum.UserInputType.MouseMovement

    if sameTouch or mouseMove then
        active.move(Vector2.new(input.Position.X, input.Position.Y))
    end
end)

connect(UserInputService.InputEnded, function(input)
    local active = dragging
    if not active then
        return
    end

    local sameTouch = input == active.input
    local mouseEnd =
        active.input.UserInputType == Enum.UserInputType.MouseButton1
        and input.UserInputType == Enum.UserInputType.MouseButton1

    if sameTouch or mouseEnd then
        dragging = nil
        unlockCamera()

        if active.finish then
            active.finish()
        end
    end
end)

connect(titleBar.InputBegan, function(input)
    if not isPointer(input) then
        return
    end

    local start = Vector2.new(input.Position.X, input.Position.Y)
    local origin = window.Position

    beginDrag(input, function(position)
        local camera = workspace.CurrentCamera
        if not camera then
            return
        end

        local delta = position - start
        local viewport = camera.ViewportSize

        window.Position = UDim2.fromOffset(
            math.clamp(
                origin.X.Offset + delta.X,
                0,
                math.max(0, viewport.X - window.AbsoluteSize.X)
            ),
            math.clamp(
                origin.Y.Offset + delta.Y,
                0,
                math.max(0, viewport.Y - window.AbsoluteSize.Y)
            )
        )
    end)
end)

-- Preview rig and gizmos ------------------------------------------------------

local moveHandles = make("Handles", {
    Name = "PoseMoveHandles",
    Style = Enum.HandlesStyle.Movement,
    Color3 = COLORS.Accent,
    Visible = false,
}, playerGui)

local rotateHandles = make("ArcHandles", {
    Name = "PoseRotateHandles",
    Color3 = COLORS.Accent,
    Visible = false,
}, playerGui)

local selectionBox = make("SelectionBox", {
    Name = "PoseSelection",
    Color3 = COLORS.Accent,
    LineThickness = 0.025,
    SurfaceTransparency = 1,
    Visible = true,
}, workspace)

local function updateGizmos()
    local part = previewParts[selectedPart]
    local editable = part ~= nil and not playing and not outputPanel.Visible

    moveHandles.Adornee = part
    rotateHandles.Adornee = part
    selectionBox.Adornee = part

    moveHandles.Visible = editable and mode == "Move"
    rotateHandles.Visible = editable and mode == "Rotate"
    selectionBox.Visible = part ~= nil and not outputPanel.Visible
end

buildPreview = function()
    local character = player.Character
    local humanoid = character and character:FindFirstChildOfClass("Humanoid")
    local root = character and character:FindFirstChild("HumanoidRootPart")

    if not character or not root or not humanoid then
        status("Character is not ready. Use Rebuild Preview.")
        return
    end

    if humanoid.RigType ~= Enum.HumanoidRigType.R6 then
        status("R6 required. Use Set R6, then rebuild after the character changes.")
        return
    end

    local oldArchivable = character.Archivable
    character.Archivable = true

    local ok, clone = pcall(function()
        return character:Clone()
    end)

    character.Archivable = oldArchivable

    if not ok or not clone then
        status("Cannot clone this character.")
        return
    end

    if ghost then
        ghost:Destroy()
    end

    ghost = clone
    ghost.Name = "LocalPosePreview"

    table.clear(previewParts)
    table.clear(joints)
    table.clear(jointByPart)
    table.clear(previewBases)

    local allowed = { HumanoidRootPart = true }

    for _, name in ipairs(PARTS) do
        allowed[name] = true
    end

    for _, child in ipairs(ghost:GetChildren()) do
        if child:IsA("BasePart") and allowed[child.Name] then
            previewParts[child.Name] = child
        end
    end

    for _, object in ipairs(ghost:GetDescendants()) do
        if object:IsA("Motor6D")
            and object.Part0
            and object.Part1
            and previewParts[object.Part0.Name] == object.Part0
            and previewParts[object.Part1.Name] == object.Part1
        then
            local joint = {
                parent = object.Part0.Name,
                child = object.Part1.Name,
                c0 = object.C0,
                c1 = object.C1,
            }

            joints[#joints + 1] = joint
            jointByPart[joint.child] = joint
        end
    end

    for _, object in ipairs(ghost:GetDescendants()) do
        if object:IsA("LuaSourceContainer")
            or object:IsA("Humanoid")
            or object:IsA("AnimationController")
            or object:IsA("JointInstance")
            or object:IsA("Constraint")
            or object:IsA("BodyMover")
        then
            object:Destroy()
        end
    end

    for _, child in ipairs(ghost:GetChildren()) do
        if child:IsA("Accessory") or child:IsA("Tool") then
            child:Destroy()
        end
    end

    for _, object in ipairs(ghost:GetDescendants()) do
        if object:IsA("BasePart") then
            if previewParts[object.Name] ~= object then
                object:Destroy()
            else
                object.Anchored = true
                object.CanCollide = false
                object.CanTouch = false
                object.CanQuery = false

                if object.Name == "HumanoidRootPart" then
                    object.Transparency = 1
                else
                    object.LocalTransparencyModifier = 0
                end
            end
        end
    end

    previewOrigin = root.CFrame * CFrame.new(CONFIG.PREVIEW_OFFSET)
    ghost.Parent = workspace

    updateGizmos()
    status("Preview rebuilt from the current R6 bind pose.")
end

local function renderPreview(poses)
    local root = previewParts.HumanoidRootPart
    if not root or not root.Parent then
        return
    end

    root.CFrame = previewOrigin

    local solved = {
        HumanoidRootPart = previewOrigin,
    }

    for _ = 1, #joints do
        local progressed = false

        for _, joint in ipairs(joints) do
            if not solved[joint.child] and solved[joint.parent] then
                local pose = poses[joint.child] or {
                    position = Vector3.zero,
                    rotation = CFrame.identity,
                }

                local basis = solved[joint.parent] * joint.c0

                local result =
                    basis
                    * CFrame.new(pose.position)
                    * pose.rotation
                    * joint.c1:Inverse()

                solved[joint.child] = result
                previewBases[joint.child] = basis

                local part = previewParts[joint.child]
                if part then
                    part.CFrame = result
                end

                progressed = true
            end
        end

        if not progressed then
            break
        end
    end
end

-- Remotes --------------------------------------------------------------------

local function resolveRemotes()
    local storage = game:GetService("ReplicatedStorage")
    local dependencies = storage:FindFirstChild("PoseEditorDependencies")
    local avatar = storage:FindFirstChild("Avatar")
    local avatarRemotes = avatar and avatar:FindFirstChild("Remotes")

    remotes.move = dependencies
        and dependencies:FindFirstChild("ChangeOffsetForPart")

    remotes.rotate = dependencies
        and dependencies:FindFirstChild("ChangeTransformationForPart")

    remotes.reset = dependencies
        and dependencies:FindFirstChild("HideAllPoses")

    remotes.rig = avatarRemotes
        and avatarRemotes:FindFirstChild("ChangeRigType")
end

local function isRemote(object)
    return object ~= nil and object:IsA("RemoteEvent")
end

local function clearRemoteCache()
    table.clear(remoteCache)
    remoteAccumulator = 0
end

local function sendPose(poses)
    if not isRemote(remotes.move) or not isRemote(remotes.rotate) then
        live = false
        refreshButtons()
        status("Pose remotes are missing or are not RemoteEvents.")
        return
    end

    local ok, err = pcall(function()
        for _, name in ipairs(PARTS) do
            local pose = poses[name]
            local previous = remoteCache[name]

            local positionChanged = not previous
                or (pose.position - previous.position).Magnitude > 0.0001

            local rotationChanged = not previous

            if previous then
                local _, angle =
                    previous.rotation:ToObjectSpace(pose.rotation):ToAxisAngle()

                rotationChanged = math.abs(angle) > 0.0001
            end

            -- Axis fix: the server expects X/Y swapped and Z inverted.
            -- Position and rotation are remapped together so the
            -- applied result matches the local preview exactly.
            if positionChanged then
                remotes.move:FireServer(name, fixPositionForRemote(pose.position))
            end

            if rotationChanged then
                remotes.rotate:FireServer(name, fixRotationForRemote(pose.rotation))
            end

            if positionChanged or rotationChanged then
                remoteCache[name] = {
                    position = pose.position,
                    rotation = pose.rotation,
                }
            end
        end
    end)

    if not ok then
        live = false
        refreshButtons()
        status("Live stopped: " .. tostring(err))
    end
end

resolveRemotes()

-- Timeline -------------------------------------------------------------------

local ROW_HEIGHT = 28
local RULER_HEIGHT = 24
local TIMELINE_HEIGHT = RULER_HEIGHT + #PARTS * ROW_HEIGHT + 10
local PLAYHEAD_MARGIN = 8
local playhead

local function screenToTime(x)
    return editTime(
        (
            x
            - timeline.AbsolutePosition.X
            + timeline.CanvasPosition.X
            - PLAYHEAD_MARGIN
        ) / zoom
    )
end

local function selectPart(name)
    selectedPart = name
    refreshTimeline()
    refreshInspector()
    refreshButtons()
    updateGizmos()
end

local function scrubInput(input, name)
    if not isPointer(input) or dragging then
        return
    end

    playing = false

    if name then
        selectedPart = name
    end

    currentTime = screenToTime(input.Position.X)

    refreshInspector()
    refreshButtons()
    updateGizmos()

    local previousScrolling = timeline.ScrollingEnabled
    timeline.ScrollingEnabled = false

    beginDrag(input, function(position)
        currentTime = screenToTime(position.X)
        refreshInspector()
    end, function()
        timeline.ScrollingEnabled = previousScrolling
        refreshTimeline()
    end)
end

refreshTimeline = function()
    if not alive then
        return
    end

    timelineContent:ClearAllChildren()
    namesContent:ClearAllChildren()

    local width = math.max(
        timeline.AbsoluteSize.X - 8,
        project.duration * zoom + PLAYHEAD_MARGIN * 2
    )

    timeline.CanvasSize = UDim2.fromOffset(width, TIMELINE_HEIGHT)
    timelineContent.Size = UDim2.fromOffset(width, TIMELINE_HEIGHT)
    namesContent.Size = UDim2.fromOffset(100, TIMELINE_HEIGHT)

    local ruler = make("TextButton", {
        Size = UDim2.fromOffset(width, RULER_HEIGHT),
        BackgroundColor3 = COLORS.Window,
        BorderSizePixel = 0,
        Text = "",
        AutoButtonColor = false,
        ZIndex = 1,
    }, timelineContent)

    ruler.InputBegan:Connect(function(input)
        scrubInput(input)
    end)

    make("TextLabel", {
        Size = UDim2.fromOffset(98, RULER_HEIGHT),
        BackgroundTransparency = 1,
        Text = "R6 Tracks",
        TextColor3 = COLORS.Muted,
        Font = Enum.Font.Gotham,
        TextSize = 10,
    }, namesContent)

    local tickInterval = zoom >= 130 and 0.5 or (zoom >= 55 and 1 or 2)

    for index = 0, math.floor(project.duration / tickInterval) do
        local tickTime = index * tickInterval
        local x = PLAYHEAD_MARGIN + tickTime * zoom

        make("Frame", {
            Position = UDim2.fromOffset(x, RULER_HEIGHT),
            Size = UDim2.fromOffset(1, TIMELINE_HEIGHT - RULER_HEIGHT),
            BackgroundColor3 = COLORS.Border,
            BackgroundTransparency = 0.6,
            BorderSizePixel = 0,
            ZIndex = 2,
        }, timelineContent)

        make("TextLabel", {
            Position = UDim2.fromOffset(x + 3, 0),
            Size = UDim2.fromOffset(45, RULER_HEIGHT),
            BackgroundTransparency = 1,
            Text = string.format("%g", tickTime),
            TextColor3 = COLORS.Muted,
            TextSize = 10,
            Font = Enum.Font.Code,
            TextXAlignment = Enum.TextXAlignment.Left,
            ZIndex = 2,
        }, timelineContent)
    end

    for rowIndex, name in ipairs(PARTS) do
        local y = RULER_HEIGHT + (rowIndex - 1) * ROW_HEIGHT
        local selected = name == selectedPart

        local nameButton = button(namesContent, name, 98)
        nameButton.Position = UDim2.fromOffset(0, y)
        nameButton.Size = UDim2.fromOffset(98, ROW_HEIGHT - 1)
        nameButton.TextSize = 10
        nameButton.BackgroundColor3 =
            selected and COLORS.Selected or COLORS.Panel

        nameButton.Activated:Connect(function()
            selectPart(name)
        end)

        local row = make("TextButton", {
            Position = UDim2.fromOffset(0, y),
            Size = UDim2.fromOffset(width, ROW_HEIGHT - 1),
            BackgroundColor3 = selected and COLORS.Selected or COLORS.Field,
            BackgroundTransparency = selected and 0.25 or 0.65,
            BorderSizePixel = 0,
            Text = "",
            AutoButtonColor = false,
            ZIndex = 1,
        }, timelineContent)

        row.InputBegan:Connect(function(input)
            scrubInput(input, name)
        end)

        for _, key in ipairs(project.tracks[name]) do
            local dot = make("TextButton", {
                AnchorPoint = Vector2.new(0.5, 0.5),
                Position = UDim2.fromOffset(
                    PLAYHEAD_MARGIN + key.t * zoom,
                    y + ROW_HEIGHT / 2
                ),
                Size = UDim2.fromOffset(14, 14),
                Rotation = 45,
                BackgroundColor3 =
                    selected and math.abs(key.t - currentTime) < 0.0001
                    and COLORS.Accent
                    or COLORS.Key,
                BorderSizePixel = 0,
                Text = "",
                AutoButtonColor = false,
                ZIndex = 5,
            }, timelineContent)

            dot.InputBegan:Connect(function(input)
                if not isPointer(input) or dragging then
                    return
                end

                playing = false
                selectedPart = name
                currentTime = key.t

                refreshInspector()
                refreshButtons()
                updateGizmos()

                local originalTime = key.t
                local targetTime = originalTime
                local startX = input.Position.X
                local previousScrolling = timeline.ScrollingEnabled

                timeline.ScrollingEnabled = false

                beginDrag(input, function(position)
                    targetTime = editTime(
                        originalTime + (position.X - startX) / zoom
                    )

                    currentTime = targetTime

                    dot.Position = UDim2.fromOffset(
                        PLAYHEAD_MARGIN + targetTime * zoom,
                        y + ROW_HEIGHT / 2
                    )

                    refreshInspector()
                end, function()
                    timeline.ScrollingEnabled = previousScrolling

                    if math.abs(targetTime - originalTime) > 0.0001 then
                        pushUndo()

                        local track = project.tracks[name]

                        for index = #track, 1, -1 do
                            local candidate = track[index]

                            if candidate ~= key
                                and math.abs(candidate.t - targetTime) < 0.0001
                            then
                                table.remove(track, index)
                            end
                        end

                        key.t = targetTime
                        sortTrack(name)
                    end

                    finishEdit()
                end)
            end)
        end
    end

    playhead = make("Frame", {
        Position = UDim2.fromOffset(
            PLAYHEAD_MARGIN + currentTime * zoom,
            0
        ),
        Size = UDim2.fromOffset(2, TIMELINE_HEIGHT),
        BackgroundColor3 = COLORS.Accent,
        BorderSizePixel = 0,
        ZIndex = 8,
    }, timelineContent)
end

connect(timeline:GetPropertyChangedSignal("CanvasPosition"), function()
    namesContent.Position = UDim2.fromOffset(0, -timeline.CanvasPosition.Y)
end)

-- Inspector ------------------------------------------------------------------

local function setBoxUnlessFocused(box, text)
    if not box:IsFocused() then
        box.Text = text
    end
end

refreshInspector = function()
    local pose = evaluateTrack(project.tracks[selectedPart], currentTime)
    local angles = rotationToArray(pose.rotation)

    local values = {
        PX = pose.position.X,
        PY = pose.position.Y,
        PZ = pose.position.Z,
        RX = angles[1],
        RY = angles[2],
        RZ = angles[3],
    }

    inspectorTitle.Text = selectedPart

    for name, value in pairs(values) do
        setBoxUnlessFocused(poseFields[name], string.format("%.3f", value))
    end

    setBoxUnlessFocused(timeBox, string.format("%.3f", currentTime))
    setBoxUnlessFocused(durationBox, tostring(project.duration))
    setBoxUnlessFocused(fpsBox, tostring(project.fps))

    local key = findKey(selectedPart, currentTime)
    easingButton.Text = key and key.e or "Linear"
    directionButton.Text = key and key.d or "InOut"
end

refreshButtons = function()
    playButton.Text = playing and "Pause" or "Play"
    loopButton.Text = looping and "Loop: On" or "Loop: Off"
    liveButton.Text = live and "Live: On" or "Live: Off"
    snapButton.Text = snapping and "Snap: On" or "Snap: Off"

    liveButton.BackgroundColor3 = live and COLORS.Selected or COLORS.Field
    moveButton.BackgroundColor3 = mode == "Move" and COLORS.Selected or COLORS.Field
    rotateButton.BackgroundColor3 = mode == "Rotate" and COLORS.Selected or COLORS.Field

    for axis, axisButton in pairs(axisButtons) do
        axisButton.BackgroundColor3 =
            axis == selectedAxis and COLORS[axis] or COLORS.Field
    end

    axisPad.Text = "Drag " .. selectedAxis .. " (" .. mode .. ")"

    undoButton.TextColor3 = #undoStack > 0 and COLORS.Text or COLORS.Muted
    redoButton.TextColor3 = #redoStack > 0 and COLORS.Text or COLORS.Muted

    updateGizmos()
end

for fieldName, box in pairs(poseFields) do
    connect(box.FocusLost, function()
        local value = finiteNumber(box.Text)

        if not value then
            refreshInspector()
            return
        end

        prepareEdit()

        local key = ensureKey(selectedPart)
        local index = ({
            PX = 1, PY = 2, PZ = 3,
            RX = 1, RY = 2, RZ = 3,
        })[fieldName]

        if string.sub(fieldName, 1, 1) == "P" then
            key.p[index] = math.clamp(value, -1000, 1000)
        else
            key.r[index] = math.clamp(value, -36000, 36000)
        end

        finishEdit()
    end)
end

local easingStyles = Enum.EasingStyle:GetEnumItems()
local easingDirections = { "In", "Out", "InOut" }

connect(easingButton.Activated, function()
    prepareEdit()
    local key = ensureKey(selectedPart)

    for index, style in ipairs(easingStyles) do
        if style.Name == key.e then
            key.e = easingStyles[index % #easingStyles + 1].Name
            break
        end
    end

    finishEdit()
end)

connect(directionButton.Activated, function()
    prepareEdit()
    local key = ensureKey(selectedPart)

    for index, direction in ipairs(easingDirections) do
        if direction == key.d then
            key.d = easingDirections[index % #easingDirections + 1]
            break
        end
    end

    finishEdit()
end)

-- Move / Rotate manipulation --------------------------------------------------

local axisVectors = {
    X = Vector3.xAxis,
    Y = Vector3.yAxis,
    Z = Vector3.zAxis,
}

local gizmoEdit
local gizmoCameraLocked = false

local function startPoseGesture()
    if playing or not previewParts[selectedPart] then
        return nil
    end

    prepareEdit()

    local key = ensureKey(selectedPart)
    local pose = poseFromKey(key)
    local joint = jointByPart[selectedPart]

    return {
        name = selectedPart,
        key = key,
        position = pose.position,
        rotation = pose.rotation,
        partFrame = previewParts[selectedPart].CFrame,
        basis = previewBases[selectedPart] or CFrame.identity,
        c1Rotation = joint and joint.c1.Rotation or CFrame.identity,
    }
end

local function applyLocalRotation(edit, axis, radians)
    local c1 = edit.c1Rotation

    return edit.rotation
        * c1:Inverse()
        * CFrame.fromAxisAngle(axis, radians)
        * c1
end

local function beginGizmoDrag()
    if dragging or gizmoEdit then
        return
    end

    gizmoEdit = startPoseGesture()

    if gizmoEdit then
        -- Lock the camera so touch drags on the gizmo cannot rotate
        -- the view at the same time.
        lockCamera()
        gizmoCameraLocked = true
    end
end

local function endGizmo()
    if gizmoEdit then
        gizmoEdit = nil

        if gizmoCameraLocked then
            gizmoCameraLocked = false
            unlockCamera()
        end

        finishEdit()
    end
end

connect(moveHandles.MouseButton1Down, beginGizmoDrag)

connect(moveHandles.MouseDrag, function(face, distance)
    local edit = gizmoEdit
    if not edit then
        return
    end

    if snapping then
        distance = round(distance, CONFIG.MOVE_STEP)
    end

    local localAxis = Vector3.FromNormalId(face)
    local worldDelta = edit.partFrame:VectorToWorldSpace(localAxis * distance)
    local offsetDelta = edit.basis:VectorToObjectSpace(worldDelta)

    setPoseKey(
        edit.key,
        edit.position + offsetDelta,
        edit.rotation
    )

    refreshInspector()
end)

connect(rotateHandles.MouseButton1Down, beginGizmoDrag)

connect(rotateHandles.MouseDrag, function(axis, relativeAngle)
    local edit = gizmoEdit
    if not edit then
        return
    end

    local degrees = math.deg(relativeAngle)

    if snapping then
        degrees = round(degrees, CONFIG.ROTATE_STEP)
    end

    local vector = axisVectors[axis.Name]

    if vector then
        setPoseKey(
            edit.key,
            edit.position,
            applyLocalRotation(edit, vector, math.rad(degrees))
        )

        refreshInspector()
    end
end

connect(moveHandles.MouseButton1Up, endGizmo)
connect(rotateHandles.MouseButton1Up, endGizmo)

connect(UserInputService.InputEnded, function(input)
    if input.UserInputType == Enum.UserInputType.MouseButton1
        or input.UserInputType == Enum.UserInputType.Touch
    then
        endGizmo()
    end
end)

connect(axisPad.InputBegan, function(input)
    if not isPointer(input) or dragging then
        return
    end

    local edit = startPoseGesture()
    if not edit then
        return
    end

    local origin = Vector2.new(input.Position.X, input.Position.Y)
    local gestureMode = mode
    local gestureAxis = selectedAxis
    local axis = axisVectors[gestureAxis]
    local previousScrolling = tools.ScrollingEnabled

    tools.ScrollingEnabled = false

    beginDrag(input, function(position)
        local delta = position - origin
        local pixels = delta.X - delta.Y

        if gestureMode == "Move" then
            local amount = pixels * CONFIG.MOBILE_MOVE_PER_PIXEL

            if snapping then
                amount = round(amount, CONFIG.MOVE_STEP)
            end

            -- Mobile move axes are the offset coordinate axes.
            setPoseKey(
                edit.key,
                edit.position + axis * amount,
                edit.rotation
            )
        else
            local degrees = pixels * CONFIG.MOBILE_ROTATE_PER_PIXEL

            if snapping then
                degrees = round(degrees, CONFIG.ROTATE_STEP)
            end

            setPoseKey(
                edit.key,
                edit.position,
                applyLocalRotation(edit, axis, math.rad(degrees))
            )
        end

        refreshInspector()
    end, function()
        tools.ScrollingEnabled = previousScrolling
        finishEdit()
    end)
end)

connect(moveButton.Activated, function()
    mode = "Move"
    refreshButtons()
end)

connect(rotateButton.Activated, function()
    mode = "Rotate"
    refreshButtons()
end)

for axis, axisButton in pairs(axisButtons) do
    connect(axisButton.Activated, function()
        selectedAxis = axis
        refreshButtons()
    end)
end

-- Editor actions --------------------------------------------------------------

local function togglePlayback()
    if dragging or gizmoEdit then
        return
    end

    if not playing and currentTime >= project.duration then
        currentTime = 0
    end

    playing = not playing
    refreshButtons()
end

connect(playButton.Activated, togglePlayback)

connect(stopButton.Activated, function()
    playing = false
    currentTime = 0
    refreshInspector()
    refreshButtons()
end)

connect(loopButton.Activated, function()
    looping = not looping
    refreshButtons()
end)

connect(liveButton.Activated, function()
    resolveRemotes()

    if not live and (
        not isRemote(remotes.move)
        or not isRemote(remotes.rotate)
    ) then
        status("Cannot enable Live: required pose remotes were not found.")
        return
    end

    live = not live
    clearRemoteCache()
    refreshButtons()

    status(live
        and "Live enabled. Changed poses are sent to the server."
        or "Live disabled. Preview remains local."
    )
end)

connect(addButton.Activated, function()
    prepareEdit()
    ensureKey(selectedPart)
    finishEdit()
end)

connect(addAllButton.Activated, function()
    prepareEdit()

    for _, name in ipairs(PARTS) do
        ensureKey(name)
    end

    finishEdit()
end)

local function deleteSelectedKey()
    local _, index = findKey(selectedPart, currentTime)

    if not index then
        status("Select a keyframe first.")
        return
    end

    prepareEdit()
    table.remove(project.tracks[selectedPart], index)
    finishEdit()
end

connect(deleteButton.Activated, deleteSelectedKey)

local function undo()
    if #undoStack == 0 or dragging or gizmoEdit then
        return
    end

    playing = false
    table.insert(redoStack, deepCopy(project))
    project = table.remove(undoStack)
    currentTime = math.clamp(currentTime, 0, project.duration)
    clearRemoteCache()
    finishEdit()
end

local function redo()
    if #redoStack == 0 or dragging or gizmoEdit then
        return
    end

    playing = false
    table.insert(undoStack, deepCopy(project))
    project = table.remove(redoStack)
    currentTime = math.clamp(currentTime, 0, project.duration)
    clearRemoteCache()
    finishEdit()
end

connect(undoButton.Activated, undo)
connect(redoButton.Activated, redo)

connect(resetButton.Activated, function()
    if os.clock() > resetArmedUntil then
        resetArmedUntil = os.clock() + 3
        resetButton.Text = "Confirm"
        status("Press Reset again within 3 seconds to clear all tracks.")
        return
    end

    prepareEdit()

    for _, name in ipairs(PARTS) do
        project.tracks[name] = {}
    end

    currentTime = 0
    resetArmedUntil = 0
    resetButton.Text = "Reset"
    clearRemoteCache()
    finishEdit()
    status("Project reset. Undo is available.")
end)

connect(snapButton.Activated, function()
    snapping = not snapping
    refreshButtons()
end)

connect(timeBox.FocusLost, function()
    local value = finiteNumber(timeBox.Text)

    if value then
        playing = false
        currentTime = editTime(value)
    end

    finishEdit()
end)

connect(durationBox.FocusLost, function()
    local value = finiteNumber(durationBox.Text)

    if value then
        value = math.clamp(value, 0.1, CONFIG.MAX_DURATION)

        local latestKey = 0

        for _, name in ipairs(PARTS) do
            for _, key in ipairs(project.tracks[name]) do
                latestKey = math.max(latestKey, key.t)
            end
        end

        if value < latestKey then
            status("Duration cannot be shorter than the last keyframe.")
        elseif value ~= project.duration then
            prepareEdit()
            project.duration = value
            currentTime = math.min(currentTime, value)
        end
    end

    finishEdit()
end)

connect(speedBox.FocusLost, function()
    local value = finiteNumber(speedBox.Text)

    if value then
        speed = math.clamp(value, 0.05, 8)
    end

    speedBox.Text = tostring(speed)
end)

connect(fpsBox.FocusLost, function()
    local value = finiteNumber(fpsBox.Text)

    if value then
        prepareEdit()
        project.fps = math.clamp(math.round(value), 1, 120)
    end

    finishEdit()
end)

connect(zoomBox.FocusLost, function()
    local value = finiteNumber(zoomBox.Text)

    if value then
        local centerTime =
            (timeline.CanvasPosition.X + timeline.AbsoluteSize.X / 2) / zoom

        zoom = math.clamp(value, 20, 300)
        refreshTimeline()

        timeline.CanvasPosition = Vector2.new(
            math.max(0, centerTime * zoom - timeline.AbsoluteSize.X / 2),
            timeline.CanvasPosition.Y
        )
    end

    zoomBox.Text = tostring(zoom)
end)

connect(moveStepBox.FocusLost, function()
    local value = finiteNumber(moveStepBox.Text)

    if value then
        CONFIG.MOVE_STEP = math.clamp(value, 0.001, 100)
    end

    moveStepBox.Text = tostring(CONFIG.MOVE_STEP)
end)

connect(rotateStepBox.FocusLost, function()
    local value = finiteNumber(rotateStepBox.Text)

    if value then
        CONFIG.ROTATE_STEP = math.clamp(value, 0.1, 180)
    end

    rotateStepBox.Text = tostring(CONFIG.ROTATE_STEP)
end)

connect(rigButton.Activated, function()
    resolveRemotes()

    if not isRemote(remotes.rig) then
        status("ChangeRigType RemoteEvent was not found.")
        return
    end

    playing = false
    live = false
    refreshButtons()

    local ok = pcall(function()
        remotes.rig:FireServer(Enum.HumanoidRigType.R6)
    end)

    status(ok
        and "R6 requested. Rebuild when the character is ready."
        or "Could not request R6."
    )

    task.delay(1.5, function()
        if alive then
            buildPreview()
        end
    end)
end)

connect(rebuildButton.Activated, buildPreview)

connect(resetRemoteButton.Activated, function()
    resolveRemotes()

    if not isRemote(remotes.reset) then
        status("HideAllPoses RemoteEvent was not found.")
        return
    end

    playing = false
    live = false
    refreshButtons()
    clearRemoteCache()

    local ok = pcall(function()
        remotes.reset:FireServer()
    end)

    status(ok
        and "Remote reset requested. Project unchanged; Live is off."
        or "Remote reset request failed."
    )
end)

connect(player.CharacterAdded, function(character)
    playing = false
    live = false
    clearRemoteCache()

    if ghost then
        ghost:Destroy()
        ghost = nil
    end

    table.clear(previewParts)
    refreshButtons()
    status("Character changed. Waiting for the R6 rig.")

    task.spawn(function()
        local root = character:WaitForChild("HumanoidRootPart", 10)
        local humanoid = character:WaitForChild("Humanoid", 10)

        if alive and root and humanoid and player.Character == character then
            task.wait(0.3)

            if alive and player.Character == character then
                buildPreview()
            end
        end
    end)
end)

-- Export ---------------------------------------------------------------------

local LIBRARY_SOURCE = [=[
local RunService = game:GetService("RunService")
local TweenService = game:GetService("TweenService")

local Animation = {
    Data = DATA,
}

local PARTS = {
    "Head", "Torso",
    "Right Arm", "Left Arm",
    "Right Leg", "Left Leg",
}

local function unpackKey(key)
    return {
        position = Vector3.new(key.p[1], key.p[2], key.p[3]),
        rotation = CFrame.Angles(
            math.rad(key.r[1]),
            math.rad(key.r[2]),
            math.rad(key.r[3])
        ),
    }
end

local function sampleTrack(track, time)
    if #track == 0 then
        return {
            position = Vector3.zero,
            rotation = CFrame.identity,
        }
    end

    if time <= track[1].t then
        return unpackKey(track[1])
    end

    if time >= track[#track].t then
        return unpackKey(track[#track])
    end

    for index = 1, #track - 1 do
        local first = track[index]
        local second = track[index + 1]

        if time >= first.t and time <= second.t then
            local alpha = (time - first.t) / (second.t - first.t)

            alpha = TweenService:GetValue(
                alpha,
                Enum.EasingStyle[first.e or "Linear"],
                Enum.EasingDirection[first.d or "InOut"]
            )

            local a = unpackKey(first)
            local b = unpackKey(second)

            return {
                position = a.position:Lerp(b.position, alpha),
                rotation = a.rotation:Lerp(b.rotation, alpha),
            }
        end
    end

    return unpackKey(track[#track])
end

function Animation.Sample(time)
    local poses = {}
    time = math.clamp(time, 0, DATA.duration)

    for _, name in ipairs(PARTS) do
        poses[name] = sampleTrack(DATA.tracks[name] or {}, time)
    end

    return poses
end

-- apply(poses, time)
-- Returns a stop function.
function Animation.Play(apply, options)
    assert(type(apply) == "function", "An apply callback is required.")

    options = options or {}

    local speed = math.clamp(tonumber(options.speed) or 1, 0.05, 8)
    local looping = options.loop == true
    local hz = math.max(0, tonumber(options.hz) or 0)

    local duration = math.max(0.001, DATA.duration)
    local elapsed = 0
    local accumulator = 0
    local active = true
    local connection

    local function stop()
        active = false

        if connection then
            connection:Disconnect()
            connection = nil
        end
    end

    local function emit(time)
        local ok, err = pcall(apply, Animation.Sample(time), time)

        if not ok then
            stop()
            warn("Animation playback stopped: " .. tostring(err))
        end
    end

    emit(0)

    if not active then
        return stop
    end

    connection = RunService.Heartbeat:Connect(function(dt)
        elapsed += dt * speed
        accumulator += dt

        local ended = not looping and elapsed >= duration
        local time = looping and (elapsed % duration)
            or math.min(elapsed, duration)

        if hz == 0 or accumulator >= 1 / hz or ended then
            accumulator = hz > 0 and (accumulator % (1 / hz)) or 0
            emit(time)
        end

        if ended then
            stop()
        end
    end)

    return stop
end

return Animation
]=]

local REMOTE_PLAYBACK_SOURCE = [=[
local ReplicatedStorage = game:GetService("ReplicatedStorage")
local dependencies = ReplicatedStorage:WaitForChild(
    "PoseEditorDependencies",
    10
)

assert(dependencies, "PoseEditorDependencies not found.")

local move = dependencies:WaitForChild("ChangeOffsetForPart", 10)
local rotate = dependencies:WaitForChild("ChangeTransformationForPart", 10)

assert(move and move:IsA("RemoteEvent"), "Move RemoteEvent not found.")
assert(rotate and rotate:IsA("RemoteEvent"), "Rotate RemoteEvent not found.")

local PARTS = {
    "Head", "Torso",
    "Right Arm", "Left Arm",
    "Right Leg", "Left Leg",
}

-- Must match the editor: the remotes expect X/Y swapped and Z inverted.
local AXIS_FIX = CFrame.new(0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1)

local cache = {}

local stop = Animation.Play(function(poses)
    for _, name in ipairs(PARTS) do
        local pose = poses[name]
        local previous = cache[name]

        local positionChanged = not previous
            or (pose.position - previous.position).Magnitude > 0.0001

        local rotationChanged = not previous

        if previous then
            local _, angle =
                previous.rotation:ToObjectSpace(pose.rotation):ToAxisAngle()

            rotationChanged = math.abs(angle) > 0.0001
        end

        if positionChanged then
            move:FireServer(name, AXIS_FIX * pose.position)
        end

        if rotationChanged then
            rotate:FireServer(name, AXIS_FIX * pose.rotation)
        end

        if positionChanged or rotationChanged then
            cache[name] = pose
        end
    end
end, PLAYBACK_OPTIONS)

-- Call stop() to stop playback.
return stop
]=]

local function copyOrShow(text, kind)
    local clipboard

    if type(setclipboard) == "function" then
        clipboard = setclipboard
    elseif type(toclipboard) == "function" then
        clipboard = toclipboard
    elseif type(environment.setclipboard) == "function" then
        clipboard = environment.setclipboard
    end

    if clipboard then
        local ok = pcall(clipboard, text)

        if ok then
            status(kind .. " copied to clipboard.")
            return
        end
    end

    playing = false
    outputTitle.Text = kind .. " export - select and copy"
    outputBox.Text = text
    outputPanel.Visible = true
    outputScroll.CanvasPosition = Vector2.zero
    refreshButtons()

    task.defer(function()
        if alive and outputPanel.Visible then
            outputBox:CaptureFocus()
            outputBox.CursorPosition = #outputBox.Text + 1
            outputBox.SelectionStart = 1
        end
    end)

    status("Clipboard unavailable. Export opened in a selectable text box.")
end

exportProject = function(kind)
    local json = HttpService:JSONEncode(project)

    if kind == "JSON" then
        copyOrShow(json, kind)
        return
    end

    local dataHeader =
        "local DATA = game:GetService(\"HttpService\"):JSONDecode("
        .. string.format("%q", json)
        .. ")\n\n"

    local moduleSource = dataHeader .. LIBRARY_SOURCE

    if kind == "LuaAnimationLib" then
        copyOrShow(moduleSource, kind)
        return
    end

    local playbackOptions = string.format(
        "{ speed = %.6f, loop = %s, hz = %.6f }",
        speed,
        tostring(looping),
        CONFIG.REMOTE_HZ
    )

    local playbackSource = REMOTE_PLAYBACK_SOURCE:gsub(
        "PLAYBACK_OPTIONS",
        function()
            return playbackOptions
        end
    )

    local scriptSource =
        "-- Generated R6 remote animation playback.\n"
        .. "-- Run on a client with access to the matching pose remotes.\n\n"
        .. "local Animation = (function()\n"
        .. moduleSource
        .. "\nend)()\n\n"
        .. playbackSource

    copyOrShow(scriptSource, "Lua")
end

connect(jsonButton.Activated, function()
    exportProject("JSON")
end)

connect(libraryButton.Activated, function()
    exportProject("LuaAnimationLib")
end)

connect(luaButton.Activated, function()
    exportProject("Lua")
end)

connect(outputPanel:GetPropertyChangedSignal("Visible"), updateGizmos)

-- Shortcuts ------------------------------------------------------------------

connect(UserInputService.InputBegan, function(input, processed)
    if processed
        or UserInputService:GetFocusedTextBox()
        or outputPanel.Visible
        or dragging
        or gizmoEdit
    then
        return
    end

    local control =
        UserInputService:IsKeyDown(Enum.KeyCode.LeftControl)
        or UserInputService:IsKeyDown(Enum.KeyCode.RightControl)

    if control and input.KeyCode == Enum.KeyCode.Z then
        undo()
    elseif control and input.KeyCode == Enum.KeyCode.Y then
        redo()
    elseif input.KeyCode == Enum.KeyCode.Space then
        togglePlayback()
    elseif input.KeyCode == Enum.KeyCode.Delete then
        deleteSelectedKey()
    elseif input.KeyCode == Enum.KeyCode.K then
        prepareEdit()
        ensureKey(selectedPart)
        finishEdit()
    end
end)

-- Heartbeat ------------------------------------------------------------------

local inspectorAccumulator = 0

connect(RunService.Heartbeat, function(dt)
    if not alive then
        return
    end

    local reachedEnd = false

    if playing then
        currentTime += dt * speed

        if currentTime >= project.duration then
            if looping then
                currentTime %= project.duration
            else
                currentTime = project.duration
                playing = false
                reachedEnd = true
                refreshButtons()
            end
        end
    end

    local poses = evaluate(currentTime)
    renderPreview(poses)

    if live then
        remoteAccumulator += dt

        local interval = CONFIG.REMOTE_HZ > 0
            and 1 / CONFIG.REMOTE_HZ
            or 0

        if interval == 0
            or remoteAccumulator >= interval
            or reachedEnd
        then
            remoteAccumulator = interval > 0
                and (remoteAccumulator % interval)
                or 0

            sendPose(poses)
        end
    end

    if playhead and playhead.Parent then
        playhead.Position = UDim2.fromOffset(
            PLAYHEAD_MARGIN + currentTime * zoom,
            0
        )
    end

    inspectorAccumulator += dt

    if inspectorAccumulator >= 0.1 then
        inspectorAccumulator = 0
        refreshInspector()
    end

    if resetArmedUntil > 0 and os.clock() > resetArmedUntil then
        resetArmedUntil = 0
        resetButton.Text = "Reset"
    end
end)

-- Cleanup --------------------------------------------------------------------

cleanup = function()
    if not alive then
        return
    end

    alive = false
    playing = false
    live = false
    dragging = nil
    gizmoEdit = nil

    while cameraLockCount > 0 do
        unlockCamera()
    end

    for _, connection in ipairs(connections) do
        connection:Disconnect()
    end

    table.clear(connections)

    moveHandles:Destroy()
    rotateHandles:Destroy()
    selectionBox:Destroy()

    if ghost then
        ghost:Destroy()
        ghost = nil
    end

    if gui.Parent then
        gui:Destroy()
    end

    if environment[SESSION_KEY] == cleanup then
        environment[SESSION_KEY] = nil
    end

    -- Closing the editor does not reset the server pose.
end

environment[SESSION_KEY] = cleanup

connect(closeButton.Activated, cleanup)
connect(gui.Destroying, cleanup)

refreshTimeline()
refreshInspector()
refreshButtons()
buildPreview()
