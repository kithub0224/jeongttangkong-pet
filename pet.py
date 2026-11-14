"""정땅콩 데스크톱 펫 (Windows / macOS)

- 화면 아래쪽(작업 표시줄/Dock 위)을 돌아다니며 놀아요.
- 마우스를 움직이면 커서 쪽을 16방향으로 쳐다봐요.
- 클릭 1·2·4번: 하트 / 3번: 점프 / 5번 이상 연타: 화내기 / 드래그: 들어서 옮기기, 놓으면 작업 표시줄로 떨어짐 (자는 중에 옮기면 깨서 화냄)
- 움직이는 행동(산책·달리기)과 멈춰서 하는 행동이 번갈아 나와요.
- 한동안 마우스를 안 움직이면 졸다가 잠들어요. 클릭하거나 옮기면 깨요(옮기면 화냄).
- 오른쪽 클릭(또는 트레이/메뉴 막대 아이콘)으로 메뉴를 열 수 있어요.
"""
import json
import math
import os
import random
import sys
import time
import traceback

from PySide6.QtCore import Qt, QTimer, QPoint, QRect, QDir, QLockFile, QSettings
from PySide6.QtGui import QAction, QActionGroup, QCursor, QGuiApplication, QIcon, QPainter, QPixmap
from PySide6.QtWidgets import QApplication, QMenu, QSystemTrayIcon, QWidget


def asset_dir():
    base = getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__)))
    return os.path.join(base, "assets")


ASSETS = asset_dir()
FEET_RATIO = 0.937     # 프레임 높이 대비 발바닥 위치
FACE_RATIO = 0.42      # 프레임 높이 대비 얼굴 중심 위치
TICK_MS = 30
SLEEP_AFTER = 60.0     # 마우스를 이만큼(초) 안 움직이면 졸기 시작
GAZE_HOLD = 2.0        # 마우스가 멈춘 뒤 이만큼(초) 더 쳐다봄
CLICK_GAP = 0.4        # 이 간격(초) 안에 이어서 누르면 연속 클릭으로 셈

# 동작 이름: (프레임당 ms, 반복 여부)
TIMING = {
    "idle": (170, True), "walk_right": (110, True), "walk_left": (110, True),
    "run_right": (75, True), "run_left": (75, True), "jump": (85, False),
    "wave": (140, False), "joy": (120, False), "doze": (260, False),
    "sleep": (420, True), "angry": (160, False), "roll": (90, False),
    "surprise": (120, False), "love": (170, False),
    # 기존 프레임을 재사용한 보조 동작
    "land": (90, False), "fall_asleep": (320, False), "wake": (180, False), "hang": (200, True), "hang_angry": (200, True),
}
GAZE_NAMES = ["E", "ENE", "NE", "NNE", "N", "NNW", "NW", "WNW",
              "W", "WSW", "SW", "SSW", "S", "SSE", "SE", "ESE"]


class Pet(QWidget):
    def __init__(self):
        super().__init__(None, Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint | Qt.Tool)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.setAttribute(Qt.WA_ShowWithoutActivating)
        if hasattr(Qt, "WA_MacAlwaysShowToolWindow"):
            self.setAttribute(Qt.WA_MacAlwaysShowToolWindow)
        self.setWindowTitle("정땅콩")

        with open(os.path.join(ASSETS, "sheet_map.json"), encoding="utf-8") as f:
            meta = json.load(f)
        # 프레임은 시트 두 장에서 잘라 씀 (actions_sheet.png, gaze16_sheet.png)
        cell = meta["cell"]
        acts = QPixmap(os.path.join(ASSETS, "actions_sheet.png"))
        gaze = QPixmap(os.path.join(ASSETS, "gaze16_sheet.png"))
        self.raw = {}
        self.seq = {}
        for a in meta["actions"]:
            names = [f"{a['name']}_{i:02d}" for i in range(a["frames"])]
            self.seq[a["name"]] = names
            for i, n in enumerate(names):
                self.raw[n] = acts.copy(QRect(i * cell, a["row"] * cell, cell, cell))
        for d in meta["gaze"]["dirs"]:
            self.raw["gaze_" + d["name"]] = gaze.copy(QRect(d["col"] * cell, d["row"] * cell, cell, cell))
        self.seq["land"] = ["jump_07", "jump_08"]
        self.seq["fall_asleep"] = self.seq["doze"][:6]
        self.seq["wake"] = self.seq["doze"][6:]
        self.seq["hang"] = ["surprise_02"]
        self.seq["hang_angry"] = ["angry_03"]

        self.size_px = 90
        self.sleep_until = 0.0
        self.cache = {}
        self.rescale()

        # 상태
        self.mode = "idle"          # idle, anim, walk, sleep, drag, fall
        self.action = "idle"
        self.idx = 0
        self.elapsed = 0
        self.after = None
        self.walk_dir = 1
        self.walk_speed = 0.0
        self.walk_until = 0.0
        self.vy = 0.0
        self.press_pos = None
        self.win_start = None
        self.dragging = False
        self.angry_on_land = False
        self.drag_from_sleep = False
        self.next_moving = True     # 다음 자동 행동이 움직이는 행동인지
        self.click_count = 0
        self.last_click = 0.0
        now = time.monotonic()
        self.last_cursor = QCursor.pos()
        self.last_activity = now
        self.next_behavior = now + random.uniform(4, 8)
        self.gaze = None

        geo = self.geo()
        self.move(geo.right() - self.size_px - 80, self.floor_y())
        self.set_action("idle")

        self.timer = QTimer(self)
        self.timer.timeout.connect(self.tick)
        self.timer.start(TICK_MS)

        self.auto_actions = []
        self.menu = self.build_menu()
        self.tray = None
        if QSystemTrayIcon.isSystemTrayAvailable():
            self.tray = QSystemTrayIcon(QIcon(self.raw["gaze_front"]), self)
            self.tray.setToolTip("정땅콩")
            self.tray.setContextMenu(self.build_menu())
            self.tray.show()

    # ---------- 그림 ----------
    def rescale(self):
        dpr = self.devicePixelRatioF() if self.windowHandle() else QGuiApplication.primaryScreen().devicePixelRatio()
        px = int(self.size_px * dpr)
        self.cache = {}
        for n, pm in self.raw.items():
            s = pm.scaled(px, px, Qt.KeepAspectRatio, Qt.SmoothTransformation)
            s.setDevicePixelRatio(dpr)
            self.cache[n] = s
        self.setFixedSize(self.size_px, self.size_px)

    def current_name(self):
        if self.mode == "idle" and self.gaze:
            return "gaze_" + self.gaze
        frames = self.seq[self.action]
        return frames[min(self.idx, len(frames) - 1)]

    def paintEvent(self, _):
        p = QPainter(self)
        p.drawPixmap(0, 0, self.cache[self.current_name()])

    # ---------- 화면/위치 ----------
    def geo(self):
        center = self.frameGeometry().center() if self.isVisible() else QCursor.pos()
        scr = QGuiApplication.screenAt(center) or QGuiApplication.primaryScreen()
        return scr.availableGeometry()

    def floor_y(self):
        return self.geo().bottom() + 1 - int(self.size_px * FEET_RATIO)

    # ---------- 동작 ----------
    def set_action(self, name, mode=None, after=None):
        self.action = name
        self.idx = 0
        self.elapsed = 0
        self.after = after
        if mode:
            self.mode = mode
        self.update()

    def play(self, name, after=None):
        """한 번 재생하는 동작. 끝나면 after() 또는 대기 상태로."""
        self.gaze = None
        self.set_action(name, "anim", after or self.to_idle)

    def to_idle(self):
        self.set_action("idle", "idle")
        self.next_behavior = time.monotonic() + random.uniform(4, 10)

    def start_walk(self, run=False, direction=None, duration=None):
        self.gaze = None
        self.walk_dir = direction or random.choice((-1, 1))
        geo = self.geo()
        if self.x() < geo.left() + 40:
            self.walk_dir = 1
        elif self.x() > geo.right() - self.size_px - 40:
            self.walk_dir = -1
        k = self.size_px / 150
        self.walk_speed = (4.6 if run else 1.7) * k
        self.walk_until = time.monotonic() + (duration or (random.uniform(1.5, 3.5) if run else random.uniform(3, 8)))
        self.set_walk_frames(run)
        self.mode = "walk"

    def set_walk_frames(self, run):
        base = "run" if run else "walk"
        self.set_action(f"{base}_{'right' if self.walk_dir > 0 else 'left'}")

    def go_sleep(self):
        self.play("fall_asleep", after=self.start_sleep)

    def start_sleep(self):
        # 마우스를 움직여도 깨지 않음. 클릭/드래그하거나 한참 자고 나면 깸
        self.sleep_until = time.monotonic() + random.uniform(90, 180)
        self.set_action("sleep", "sleep")

    def wake_up(self):
        self.last_activity = time.monotonic()
        self.play("wake", after=self.to_idle)

    def random_behavior(self):
        """움직이는 행동과 멈춰서 하는 행동을 번갈아 실행."""
        moving, self.next_moving = self.next_moving, not self.next_moving
        if moving:
            self.start_walk(run=random.random() < 0.25)
        else:
            choice = random.choice(["wave", "joy", "jump", "roll", "love", "rest"])
            if choice == "rest":     # 가만히 서서 숨쉬기
                self.next_behavior = time.monotonic() + random.uniform(4, 7)
            else:
                self.play(choice)

    # ---------- 매 프레임 ----------
    def tick(self):
        now = time.monotonic()
        cur = QCursor.pos()
        moved = cur != self.last_cursor
        if moved:
            self.last_cursor = cur
            self.last_activity = now

        if self.click_count and now - self.last_click > CLICK_GAP:
            self.resolve_clicks()

        if self.mode == "drag":
            pass
        elif self.mode == "fall":
            self.vy += 1.4 * self.size_px / 150
            fy = self.floor_y()
            ny = self.y() + int(self.vy)
            if ny >= fy:
                self.move(self.x(), fy)
                self.vy = 0
                if self.angry_on_land:       # 자다가 옮겨진 경우: 착지 후 화내기
                    self.angry_on_land = False
                    self.play("land", after=lambda: self.play("angry"))
                else:
                    self.play("land")
            else:
                self.move(self.x(), ny)
        else:
            self.advance()
            if self.mode == "walk":
                self.walk_step(now)
            elif self.mode == "sleep":
                if now > self.sleep_until:
                    self.wake_up()
            elif self.mode == "idle":
                self.idle_step(now)

        self.update()

    def advance(self):
        ms, loop = TIMING[self.action]
        self.elapsed += TICK_MS
        if self.elapsed < ms:
            return
        self.elapsed -= ms
        n = len(self.seq[self.action])
        if self.idx + 1 < n:
            self.idx += 1
        elif loop:
            self.idx = 0
        elif self.after:
            cb, self.after = self.after, None
            cb()

    def walk_step(self, now):
        geo = self.geo()
        x = self.x() + self.walk_dir * self.walk_speed
        lo, hi = geo.left() - self.size_px * 0.15, geo.right() - self.size_px * 0.85
        if x < lo or x > hi:
            self.walk_dir *= -1
            x = max(lo, min(hi, x))
            self.set_walk_frames(self.action.startswith("run"))
        self.move(int(round(x)), self.floor_y())
        if now > self.walk_until:
            self.to_idle()

    def idle_step(self, now):
        # 커서 쳐다보기
        if now - self.last_activity < GAZE_HOLD:
            c = self.last_cursor
            fx = self.x() + self.width() / 2
            fy = self.y() + self.height() * FACE_RATIO
            dx, dy = c.x() - fx, c.y() - fy
            if math.hypot(dx, dy) < self.size_px * 0.3:
                self.gaze = "front"
            else:
                ang = math.degrees(math.atan2(-dy, dx)) % 360
                self.gaze = GAZE_NAMES[int(round(ang / 22.5)) % 16]
        else:
            self.gaze = None
        if now - self.last_activity > SLEEP_AFTER:
            self.gaze = None
            self.go_sleep()
        elif now > self.next_behavior and not self.gaze:
            self.random_behavior()

    # ---------- 마우스 ----------
    def mousePressEvent(self, e):
        if e.button() == Qt.LeftButton:
            self.press_pos = e.globalPosition().toPoint()
            self.win_start = self.pos()
            self.dragging = False

    def mouseMoveEvent(self, e):
        if not (e.buttons() & Qt.LeftButton) or self.press_pos is None:
            return
        delta = e.globalPosition().toPoint() - self.press_pos
        if not self.dragging and delta.manhattanLength() > 6:
            self.dragging = True
            self.drag_from_sleep = self.mode == "sleep" or self.action in ("fall_asleep", "wake")
            self.gaze = None
            if self.drag_from_sleep:
                self.set_action("hang_angry", "drag")
            else:
                self.set_action("hang", "drag")
        if self.dragging:
            self.move(self.win_start + delta)

    def mouseReleaseEvent(self, e):
        if e.button() != Qt.LeftButton:
            return
        self.press_pos = None
        if self.dragging:
            self.dragging = False
            # 놓으면 작업 표시줄 위로 떨어져서 착지
            self.last_activity = time.monotonic()
            self.angry_on_land = self.drag_from_sleep
            self.drag_from_sleep = False
            self.vy = 0
            self.mode = "fall"
            return
        now = time.monotonic()
        self.last_activity = now
        self.click_count = self.click_count + 1 if now - self.last_click <= CLICK_GAP else 1
        self.last_click = now
        if self.click_count >= 5:           # 연타는 바로 화내기 (계속 누르면 계속 화남)
            if self.action != "angry":
                self.play("angry")
            self.click_count = 5

    def mouseDoubleClickEvent(self, e):
        # Qt는 더블클릭 뒤에도 mouseReleaseEvent를 보내므로 거기서 한 번만 셈
        pass

    def resolve_clicks(self):
        n, self.click_count = self.click_count, 0
        if n >= 5 or self.mode == "drag":
            return
        react = "jump" if n == 3 else "love"     # 1·2·4번: 하트 / 3번: 점프
        if self.mode == "sleep":
            self.play("wake", after=lambda: self.play(react))
        else:
            self.play(react)

    def contextMenuEvent(self, e):
        self.menu.exec(e.globalPos())

    # ---------- 메뉴 ----------
    def set_autostart_option(self, on):
        save_autostart(on)
        for a in self.auto_actions:      # 펫 메뉴와 트레이 메뉴 체크 표시 맞추기
            if a.isChecked() != on:
                a.blockSignals(True)
                a.setChecked(on)
                a.blockSignals(False)

    def build_menu(self):
        m = QMenu()
        def add(text, fn):
            act = QAction(text, m)
            act.triggered.connect(fn)
            m.addAction(act)
        add("인사하기", lambda: self.play("wave"))
        add("점프", lambda: self.play("jump"))
        # 메뉴 산책: 방향은 무작위(화면 끝이면 안쪽), 자동 산책보다 조금 짧게
        add("산책하기", lambda: self.start_walk(duration=random.uniform(2.5, 5)))
        add("달리기", lambda: self.start_walk(run=True))
        add("기뻐하기", lambda: self.play("joy"))
        add("하트", lambda: self.play("love"))
        add("뒹굴기", lambda: self.play("roll"))
        add("재우기", self.go_sleep)
        m.addSeparator()
        sm = m.addMenu("크기")
        grp = QActionGroup(sm)
        for label, px in (("작게", 80), ("보통", 90), ("크게", 100), ("거대하게", 150)):
            act = QAction(label, sm)
            act.setCheckable(True)
            act.setChecked(px == 90)
            act.triggered.connect(lambda _=False, v=px: self.set_size(v))
            grp.addAction(act)
            sm.addAction(act)
        m.addSeparator()
        auto = QAction("컴퓨터 켤 때 자동 실행", m)
        auto.setCheckable(True)
        auto.setChecked(autostart_enabled())
        auto.toggled.connect(self.set_autostart_option)
        self.auto_actions.append(auto)
        m.addAction(auto)
        m.addSeparator()
        add("종료", quit_by_user)
        return m

    def set_size(self, px):
        self.size_px = px
        self.rescale()
        self.move(self.x(), self.floor_y())


APP_ID = "jeongttangkong"
MAC_PLIST = os.path.expanduser(f"~/Library/LaunchAgents/com.kithub0224.{APP_ID}.plist")


def autostart_target():
    """자동 실행에 등록할 실행 파일 경로. 빌드된 앱(exe/.app)일 때만 등록."""
    if not getattr(sys, "frozen", False):
        return None
    exe = os.path.abspath(sys.executable)
    if sys.platform == "darwin" and "/AppTranslocation/" in exe:
        return None   # 다운로드 폴더에서 바로 실행한 경우: 경로가 매번 바뀌어 등록하지 않음
    return exe


def set_autostart(on):
    """켜져 있는 동안은 컴퓨터를 켤 때 자동 실행, 메뉴로 직접 종료하면 해제."""
    try:
        if sys.platform.startswith("win"):
            import winreg
            key = winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                                 r"Software\Microsoft\Windows\CurrentVersion\Run", 0, winreg.KEY_SET_VALUE)
            if on:
                exe = autostart_target()
                if exe:
                    winreg.SetValueEx(key, APP_ID, 0, winreg.REG_SZ, f'"{exe}"')
            else:
                try:
                    winreg.DeleteValue(key, APP_ID)
                except FileNotFoundError:
                    pass
            winreg.CloseKey(key)
        elif sys.platform == "darwin":
            if on:
                exe = autostart_target()
                if exe:
                    os.makedirs(os.path.dirname(MAC_PLIST), exist_ok=True)
                    with open(MAC_PLIST, "w", encoding="utf-8") as f:
                        f.write(f"""<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0"><dict>
<key>Label</key><string>com.kithub0224.{APP_ID}</string>
<key>ProgramArguments</key><array><string>{exe}</string></array>
<key>RunAtLoad</key><true/>
</dict></plist>
""")
            elif os.path.exists(MAC_PLIST):
                os.remove(MAC_PLIST)
    except Exception:
        traceback.print_exc()   # 자동 실행 등록에 실패해도 펫은 그대로 실행


def autostart_enabled():
    # 처음 실행할 때는 켜짐이 기본값
    return QSettings("kithub0224", APP_ID).value("autostart", True, type=bool)


def save_autostart(on):
    QSettings("kithub0224", APP_ID).setValue("autostart", bool(on))
    set_autostart(on)


def quit_by_user():
    QApplication.instance().quit()


def main():
    selftest = "--selftest" in sys.argv
    if selftest:
        # 빌드 확인용: 오류가 나면 바로 실패 코드로 끝냄
        def hook(*exc):
            traceback.print_exception(*exc)
            os._exit(1)
        sys.excepthook = hook

    app = QApplication(sys.argv)
    app.setQuitOnLastWindowClosed(False)

    lock = None
    if not selftest:
        # 이미 실행 중이면 하나 더 띄우지 않음
        lock = QLockFile(os.path.join(QDir.tempPath(), APP_ID + ".lock"))
        if not lock.tryLock(100):
            return
        set_autostart(autostart_enabled())   # 설정대로 등록/해제 (exe 위치가 바뀌어도 갱신)

    pet = Pet()
    app.setWindowIcon(QIcon(pet.raw["gaze_front"]))
    pet.show()
    pet.rescale()   # 실제 화면 배율로 다시 맞춤

    if selftest:
        missing = [n for names in pet.seq.values() for n in names if pet.cache.get(n) is None or pet.cache[n].isNull()]
        if missing:
            print("missing frames:", missing)
            sys.exit(1)
        acts = ["wave", "joy", "jump", "roll", "love", "angry", "surprise"]
        for k, a in enumerate(acts):
            QTimer.singleShot(300 + k * 400, lambda a=a: pet.play(a))
        QTimer.singleShot(3200, lambda: pet.start_walk(run=True))
        QTimer.singleShot(4000, pet.go_sleep)
        QTimer.singleShot(6000, app.quit)

    code = app.exec()
    sys.exit(code)


if __name__ == "__main__":
    main()
