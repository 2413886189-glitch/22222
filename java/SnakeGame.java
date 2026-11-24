import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.SwingUtilities;
import javax.swing.Timer;
import java.awt.BasicStroke;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.FontMetrics;
import java.awt.GradientPaint;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Point;
import java.awt.RenderingHints;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.prefs.Preferences;

/**
 * 改进版 Java Swing 贪吃蛇小游戏
 *
 * 参考 GitHub 经典 Java Swing 贪吃蛇项目并进行了多项核心改进：
 * 1. FIFO 方向输入缓冲队列（最多缓冲 2 步），彻底解决快速按键掉头自撞或吞键问题
 * 2. O(N) 空位表食物生成算法，避免后期卡顿/死循环，并在满屏时触发通关胜利
 * 3. 精确尾格碰撞判定：蛇不增长时允许蛇头紧贴追尾
 * 4. 限时金色奖励食物（每吃 5 个普通食物触发，+30 分，附带倒计时条）
 * 5. 支持 3 档难度（简单/普通/困难）、穿墙/撞墙模式切换、平滑动态加速
 * 6. 本地历史最高分持久化（基于 java.util.prefs.Preferences）
 * 7. Graphics2D 抗锯齿渲染：深色棋盘、渐变圆角蛇身、方向蛇眼与状态覆盖层
 */
public class SnakeGame {

    public static void main(String[] args) {
        SwingUtilities.invokeLater(new Runnable() {
            @Override
            public void run() {
                JFrame frame = new JFrame("贪吃蛇大作战 - Java Swing 改进版");
                frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
                frame.setResizable(false);

                GamePanel panel = new GamePanel();
                frame.add(panel);
                frame.pack();
                frame.setLocationRelativeTo(null);
                frame.setVisible(true);
                panel.requestFocusInWindow();
            }
        });
    }

    enum Direction {
        UP(0, -1),
        DOWN(0, 1),
        LEFT(-1, 0),
        RIGHT(1, 0);

        final int dx;
        final int dy;

        Direction(int dx, int dy) {
            this.dx = dx;
            this.dy = dy;
        }

        boolean isOpposite(Direction other) {
            return this.dx + other.dx == 0 && this.dy + other.dy == 0;
        }
    }

    enum GameState {
        READY,
        RUNNING,
        PAUSED,
        GAME_OVER,
        VICTORY
    }

    enum Difficulty {
        EASY("简单", 155, 80),
        NORMAL("普通", 120, 62),
        HARD("困难", 90, 48);

        final String label;
        final int baseDelayMs;
        final int minDelayMs;

        Difficulty(String label, int baseDelayMs, int minDelayMs) {
            this.label = label;
            this.baseDelayMs = baseDelayMs;
            this.minDelayMs = minDelayMs;
        }

        Difficulty next() {
            Difficulty[] values = values();
            return values[(ordinal() + 1) % values.length];
        }
    }

    static class GamePanel extends JPanel implements ActionListener {
        private static final int COLS = 24;
        private static final int ROWS = 20;
        private static final int CELL_SIZE = 28;
        private static final int HUD_HEIGHT = 56;
        private static final int BOARD_WIDTH = COLS * CELL_SIZE;
        private static final int BOARD_HEIGHT = ROWS * CELL_SIZE;
        private static final int MAX_INPUT_QUEUE = 2;
        private static final int BONUS_FOOD_TRIGGER = 5;
        private static final int BONUS_FOOD_LIFETIME_TICKS = 45;

        // 配色方案（深色护眼主题）
        private static final Color BG_HUD = new Color(18, 22, 30);
        private static final Color BG_TILE_DARK = new Color(24, 30, 41);
        private static final Color BG_TILE_LIGHT = new Color(28, 35, 48);
        private static final Color BORDER_COLOR = new Color(52, 65, 85);
        private static final Color SNAKE_HEAD = new Color(52, 211, 153);
        private static final Color SNAKE_TAIL = new Color(16, 125, 92);
        private static final Color FOOD_COLOR = new Color(248, 113, 113);
        private static final Color FOOD_GLOW = new Color(248, 113, 113, 60);
        private static final Color BONUS_COLOR = new Color(251, 191, 36);
        private static final Color BONUS_GLOW = new Color(251, 191, 36, 75);
        private static final Color TEXT_PRIMARY = new Color(241, 245, 249);
        private static final Color TEXT_MUTED = new Color(148, 163, 184);
        private static final Color ACCENT_CYAN = new Color(56, 189, 248);

        private final Random random = new Random();
        private final Preferences prefs = Preferences.userNodeForPackage(SnakeGame.class);
        private static final String PREF_HIGH_SCORE = "snake_high_score";

        private final LinkedList<Point> snake = new LinkedList<Point>();
        private final Deque<Direction> directionQueue = new ArrayDeque<Direction>();
        private Direction currentDirection = Direction.RIGHT;

        private Point normalFood;
        private Point bonusFood;
        private int bonusTicksLeft = 0;
        private int foodsEatenCount = 0;

        private GameState state = GameState.READY;
        private Difficulty difficulty = Difficulty.NORMAL;
        private boolean wrapWalls = false;

        private int score = 0;
        private int highScore = 0;
        private int tickCounter = 0;

        private final Timer timer;

        GamePanel() {
            setPreferredSize(new Dimension(BOARD_WIDTH, HUD_HEIGHT + BOARD_HEIGHT));
            setBackground(BG_HUD);
            setFocusable(true);

            highScore = prefs.getInt(PREF_HIGH_SCORE, 0);
            resetGame(false);

            timer = new Timer(difficulty.baseDelayMs, this);
            timer.start();

            addKeyListener(new KeyAdapter() {
                @Override
                public void keyPressed(KeyEvent e) {
                    handleKeyPress(e.getKeyCode());
                }
            });
        }

        private void resetGame(boolean startImmediately) {
            snake.clear();
            directionQueue.clear();
            currentDirection = Direction.RIGHT;

            int startX = COLS / 2;
            int startY = ROWS / 2;
            snake.addFirst(new Point(startX, startY));
            snake.addLast(new Point(startX - 1, startY));
            snake.addLast(new Point(startX - 2, startY));

            score = 0;
            foodsEatenCount = 0;
            bonusFood = null;
            bonusTicksLeft = 0;
            normalFood = spawnSafeFood(null);

            state = startImmediately ? GameState.RUNNING : GameState.READY;
            updateTimerDelay();
            repaint();
        }

        private void updateTimerDelay() {
            if (timer == null) {
                return;
            }
            int speedBoost = (score / 30) * 4;
            int delay = Math.max(difficulty.minDelayMs, difficulty.baseDelayMs - speedBoost);
            timer.setDelay(delay);
        }

        private void handleKeyPress(int keyCode) {
            // 难度与模式切换（在开始界面、暂停或结束界面可用）
            if (state != GameState.RUNNING) {
                if (keyCode == KeyEvent.VK_1) {
                    difficulty = Difficulty.EASY;
                    updateTimerDelay();
                    repaint();
                    return;
                } else if (keyCode == KeyEvent.VK_2) {
                    difficulty = Difficulty.NORMAL;
                    updateTimerDelay();
                    repaint();
                    return;
                } else if (keyCode == KeyEvent.VK_3) {
                    difficulty = Difficulty.HARD;
                    updateTimerDelay();
                    repaint();
                    return;
                } else if (keyCode == KeyEvent.VK_M) {
                    wrapWalls = !wrapWalls;
                    repaint();
                    return;
                }
            }

            if (keyCode == KeyEvent.VK_SPACE || keyCode == KeyEvent.VK_P) {
                if (state == GameState.READY) {
                    state = GameState.RUNNING;
                } else if (state == GameState.RUNNING) {
                    state = GameState.PAUSED;
                } else if (state == GameState.PAUSED) {
                    state = GameState.RUNNING;
                } else if (state == GameState.GAME_OVER || state == GameState.VICTORY) {
                    resetGame(true);
                }
                repaint();
                return;
            }

            if (keyCode == KeyEvent.VK_ENTER || keyCode == KeyEvent.VK_R) {
                if (state == GameState.READY) {
                    state = GameState.RUNNING;
                    repaint();
                } else if (state == GameState.GAME_OVER || state == GameState.VICTORY || keyCode == KeyEvent.VK_R) {
                    resetGame(true);
                }
                return;
            }

            Direction requested = mapKeyToDirection(keyCode);
            if (requested == null) {
                return;
            }

            // 在 READY 状态按方向键可直接开局
            if (state == GameState.READY) {
                state = GameState.RUNNING;
            }
            if (state != GameState.RUNNING) {
                return;
            }

            Direction lastPlanned = directionQueue.isEmpty() ? currentDirection : directionQueue.peekLast();
            if (requested != lastPlanned && !requested.isOpposite(lastPlanned) && directionQueue.size() < MAX_INPUT_QUEUE) {
                directionQueue.addLast(requested);
            }
        }

        private Direction mapKeyToDirection(int keyCode) {
            switch (keyCode) {
                case KeyEvent.VK_UP:
                case KeyEvent.VK_W:
                    return Direction.UP;
                case KeyEvent.VK_DOWN:
                case KeyEvent.VK_S:
                    return Direction.DOWN;
                case KeyEvent.VK_LEFT:
                case KeyEvent.VK_A:
                    return Direction.LEFT;
                case KeyEvent.VK_RIGHT:
                case KeyEvent.VK_D:
                    return Direction.RIGHT;
                default:
                    return null;
            }
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            tickCounter++;
            if (state == GameState.RUNNING) {
                stepGame();
            }
            repaint();
        }

        private void stepGame() {
            if (!directionQueue.isEmpty()) {
                currentDirection = directionQueue.pollFirst();
            }

            Point head = snake.peekFirst();
            int nextX = head.x + currentDirection.dx;
            int nextY = head.y + currentDirection.dy;

            if (wrapWalls) {
                nextX = (nextX + COLS) % COLS;
                nextY = (nextY + ROWS) % ROWS;
            } else {
                if (nextX < 0 || nextX >= COLS || nextY < 0 || nextY >= ROWS) {
                    triggerGameOver();
                    return;
                }
            }

            Point nextHead = new Point(nextX, nextY);
            boolean ateNormal = nextHead.equals(normalFood);
            boolean ateBonus = bonusFood != null && nextHead.equals(bonusFood);
            boolean willGrow = ateNormal || ateBonus;

            // 精确自撞检测：如果本帧不增长，蛇尾会移走，因此允许进入当前蛇尾位置
            int checkLimit = willGrow ? snake.size() : snake.size() - 1;
            for (int i = 0; i < checkLimit; i++) {
                if (snake.get(i).equals(nextHead)) {
                    triggerGameOver();
                    return;
                }
            }

            snake.addFirst(nextHead);
            if (!willGrow) {
                snake.removeLast();
            }

            if (ateNormal) {
                score += 10;
                foodsEatenCount++;
                updateHighScore();
                updateTimerDelay();

                normalFood = spawnSafeFood(bonusFood);
                if (normalFood == null) {
                    state = GameState.VICTORY;
                    return;
                }

                if (foodsEatenCount % BONUS_FOOD_TRIGGER == 0 && bonusFood == null) {
                    bonusFood = spawnSafeFood(normalFood);
                    if (bonusFood != null) {
                        bonusTicksLeft = BONUS_FOOD_LIFETIME_TICKS;
                    }
                }
            } else if (ateBonus) {
                score += 30;
                bonusFood = null;
                bonusTicksLeft = 0;
                updateHighScore();
                updateTimerDelay();
            }

            if (bonusFood != null) {
                bonusTicksLeft--;
                if (bonusTicksLeft <= 0) {
                    bonusFood = null;
                }
            }
        }

        private void updateHighScore() {
            if (score > highScore) {
                highScore = score;
                prefs.putInt(PREF_HIGH_SCORE, highScore);
            }
        }

        private void triggerGameOver() {
            updateHighScore();
            state = GameState.GAME_OVER;
        }

        /**
         * O(N) 确定性安全食物生成：收集所有空闲格后随机选取，彻底避免后期卡顿。
         */
        private Point spawnSafeFood(Point otherFood) {
            Set<Point> occupied = new HashSet<Point>(snake);
            if (otherFood != null) {
                occupied.add(otherFood);
            }

            List<Point> freeCells = new ArrayList<Point>(COLS * ROWS - occupied.size());
            for (int x = 0; x < COLS; x++) {
                for (int y = 0; y < ROWS; y++) {
                    Point p = new Point(x, y);
                    if (!occupied.contains(p)) {
                        freeCells.add(p);
                    }
                }
            }

            if (freeCells.isEmpty()) {
                return null;
            }
            return freeCells.get(random.nextInt(freeCells.size()));
        }

        @Override
        protected void paintComponent(Graphics g) {
            super.paintComponent(g);
            Graphics2D g2 = (Graphics2D) g.create();
            g2.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
            g2.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING, RenderingHints.VALUE_TEXT_ANTIALIAS_ON);

            drawHud(g2);
            drawBoard(g2);
            drawFoods(g2);
            drawSnake(g2);

            if (state != GameState.RUNNING) {
                drawOverlay(g2);
            }

            g2.dispose();
        }

        private void drawHud(Graphics2D g2) {
            g2.setColor(BG_HUD);
            g2.fillRect(0, 0, BOARD_WIDTH, HUD_HEIGHT);

            g2.setColor(BORDER_COLOR);
            g2.drawLine(0, HUD_HEIGHT - 1, BOARD_WIDTH, HUD_HEIGHT - 1);

            g2.setFont(new Font("SansSerif", Font.BOLD, 16));
            g2.setColor(TEXT_PRIMARY);
            g2.drawString("得分: " + score, 18, 25);

            g2.setColor(BONUS_COLOR);
            g2.drawString("最高分: " + highScore, 130, 25);

            g2.setFont(new Font("SansSerif", Font.PLAIN, 13));
            g2.setColor(TEXT_MUTED);
            String modeText = wrapWalls ? "穿墙模式" : "经典撞墙";
            g2.drawString("难度: " + difficulty.label + "  |  模式: " + modeText + "  |  长度: " + snake.size(), 18, 46);

            // 金色奖励果倒计时进度条
            if (bonusFood != null && bonusTicksLeft > 0) {
                int barWidth = 140;
                int barHeight = 8;
                int barX = BOARD_WIDTH - barWidth - 18;
                int barY = 32;

                g2.setFont(new Font("SansSerif", Font.BOLD, 12));
                g2.setColor(BONUS_COLOR);
                g2.drawString("限时奖励 +30", barX, 24);

                g2.setColor(new Color(51, 65, 85));
                g2.fillRoundRect(barX, barY, barWidth, barHeight, 6, 6);

                double ratio = (double) bonusTicksLeft / BONUS_FOOD_LIFETIME_TICKS;
                int fillW = Math.max(4, (int) (barWidth * ratio));
                g2.setColor(BONUS_COLOR);
                g2.fillRoundRect(barX, barY, fillW, barHeight, 6, 6);
            } else {
                g2.setFont(new Font("SansSerif", Font.PLAIN, 12));
                g2.setColor(TEXT_MUTED);
                String hint = "空格: 暂停  |  R: 重开";
                FontMetrics fm = g2.getFontMetrics();
                g2.drawString(hint, BOARD_WIDTH - fm.stringWidth(hint) - 18, 34);
            }
        }

        private void drawBoard(Graphics2D g2) {
            for (int x = 0; x < COLS; x++) {
                for (int y = 0; y < ROWS; y++) {
                    g2.setColor(((x + y) % 2 == 0) ? BG_TILE_DARK : BG_TILE_LIGHT);
                    g2.fillRect(x * CELL_SIZE, HUD_HEIGHT + y * CELL_SIZE, CELL_SIZE, CELL_SIZE);
                }
            }

            if (wrapWalls) {
                g2.setColor(new Color(56, 189, 248, 120));
                g2.setStroke(new BasicStroke(2f, BasicStroke.CAP_BUTT, BasicStroke.JOIN_MITER, 10f, new float[]{6f, 6f}, 0f));
                g2.drawRect(1, HUD_HEIGHT + 1, BOARD_WIDTH - 3, BOARD_HEIGHT - 3);
                g2.setStroke(new BasicStroke(1f));
            }
        }

        private void drawFoods(Graphics2D g2) {
            if (normalFood != null) {
                drawOrbFood(g2, normalFood, FOOD_COLOR, FOOD_GLOW, false);
            }
            if (bonusFood != null) {
                drawOrbFood(g2, bonusFood, BONUS_COLOR, BONUS_GLOW, true);
            }
        }

        private void drawOrbFood(Graphics2D g2, Point cell, Color core, Color glow, boolean pulse) {
            int cx = cell.x * CELL_SIZE + CELL_SIZE / 2;
            int cy = HUD_HEIGHT + cell.y * CELL_SIZE + CELL_SIZE / 2;
            int pulseOffset = pulse ? (int) (Math.sin(tickCounter * 0.6) * 2) : 0;

            int glowSize = CELL_SIZE - 2 + pulseOffset;
            g2.setColor(glow);
            g2.fillOval(cx - glowSize / 2, cy - glowSize / 2, glowSize, glowSize);

            int orbSize = CELL_SIZE - 10 + pulseOffset / 2;
            g2.setColor(core);
            g2.fillOval(cx - orbSize / 2, cy - orbSize / 2, orbSize, orbSize);

            // 高光点
            g2.setColor(new Color(255, 255, 255, 160));
            g2.fillOval(cx - orbSize / 4, cy - orbSize / 4, 4, 4);
        }

        private void drawSnake(Graphics2D g2) {
            int len = snake.size();
            for (int i = len - 1; i >= 0; i--) {
                Point seg = snake.get(i);
                int px = seg.x * CELL_SIZE;
                int py = HUD_HEIGHT + seg.y * CELL_SIZE;

                float t = (len <= 1) ? 0f : (float) i / (len - 1);
                Color segColor = blendColor(SNAKE_HEAD, SNAKE_TAIL, t);

                int pad = (i == 0) ? 2 : 3;
                int size = CELL_SIZE - pad * 2;
                int arc = (i == 0) ? 10 : 8;

                if (i == 0) {
                    g2.setPaint(new GradientPaint(px, py, SNAKE_HEAD.brighter(), px + CELL_SIZE, py + CELL_SIZE, SNAKE_HEAD));
                } else {
                    g2.setColor(segColor);
                }
                g2.fillRoundRect(px + pad, py + pad, size, size, arc, arc);

                if (i == 0) {
                    drawSnakeEyes(g2, px, py);
                }
            }
        }

        private void drawSnakeEyes(Graphics2D g2, int px, int py) {
            int eyeSize = 5;
            int ex1, ey1, ex2, ey2;

            switch (currentDirection) {
                case UP:
                    ex1 = px + 6;  ey1 = py + 6;
                    ex2 = px + 17; ey2 = py + 6;
                    break;
                case DOWN:
                    ex1 = px + 6;  ey1 = py + 17;
                    ex2 = px + 17; ey2 = py + 17;
                    break;
                case LEFT:
                    ex1 = px + 6;  ey1 = py + 6;
                    ex2 = px + 6;  ey2 = py + 17;
                    break;
                case RIGHT:
                default:
                    ex1 = px + 17; ey1 = py + 6;
                    ex2 = px + 17; ey2 = py + 17;
                    break;
            }

            g2.setColor(Color.WHITE);
            g2.fillOval(ex1, ey1, eyeSize, eyeSize);
            g2.fillOval(ex2, ey2, eyeSize, eyeSize);

            g2.setColor(new Color(15, 23, 42));
            g2.fillOval(ex1 + 1, ey1 + 1, 3, 3);
            g2.fillOval(ex2 + 1, ey2 + 1, 3, 3);
        }

        private void drawOverlay(Graphics2D g2) {
            g2.setColor(new Color(15, 23, 42, 185));
            g2.fillRect(0, HUD_HEIGHT, BOARD_WIDTH, BOARD_HEIGHT);

            int centerY = HUD_HEIGHT + BOARD_HEIGHT / 2;
            String title;
            String subtitle;
            Color titleColor;

            switch (state) {
                case READY:
                    title = "贪吃蛇大作战";
                    subtitle = "按 方向键 / WASD / 空格 开始游戏";
                    titleColor = SNAKE_HEAD;
                    break;
                case PAUSED:
                    title = "游戏已暂停";
                    subtitle = "按 空格 / P 继续，按 R 重新开始";
                    titleColor = ACCENT_CYAN;
                    break;
                case VICTORY:
                    title = "恭喜通关！";
                    subtitle = "最终得分: " + score + "  |  按 空格 / R 再来一局";
                    titleColor = BONUS_COLOR;
                    break;
                case GAME_OVER:
                default:
                    title = "游戏结束";
                    subtitle = "本局得分: " + score + "  (最高分: " + highScore + ")  |  按 空格 / R 重开";
                    titleColor = FOOD_COLOR;
                    break;
            }

            drawCenteredText(g2, title, new Font("SansSerif", Font.BOLD, 34), titleColor, centerY - 40);
            drawCenteredText(g2, subtitle, new Font("SansSerif", Font.PLAIN, 16), TEXT_PRIMARY, centerY + 4);

            String controls = "按 1/2/3 切换难度（当前: " + difficulty.label + "）  |  按 M 切换模式（当前: "
                    + (wrapWalls ? "穿墙" : "撞墙") + "）";
            drawCenteredText(g2, controls, new Font("SansSerif", Font.PLAIN, 13), TEXT_MUTED, centerY + 44);
        }

        private void drawCenteredText(Graphics2D g2, String text, Font font, Color color, int y) {
            g2.setFont(font);
            g2.setColor(color);
            FontMetrics fm = g2.getFontMetrics();
            int x = (BOARD_WIDTH - fm.stringWidth(text)) / 2;
            g2.drawString(text, x, y);
        }

        private Color blendColor(Color c1, Color c2, float ratio) {
            float clamped = Math.max(0f, Math.min(1f, ratio));
            int r = (int) (c1.getRed() * (1 - clamped) + c2.getRed() * clamped);
            int g = (int) (c1.getGreen() * (1 - clamped) + c2.getGreen() * clamped);
            int b = (int) (c1.getBlue() * (1 - clamped) + c2.getBlue() * clamped);
            return new Color(r, g, b);
        }
    }
}
