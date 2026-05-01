#include <stdint.h>
#include <stdlib.h>
#include <raylib.h>
#include <stdint.h>

static const int mouse_left = 0;
static const int flag_msaa_4x = 32;
static const int empty = 0;
static const int x_piece = 1;
static const int o_piece = 2;
static const int playing = 0;
static const int won = 1;
static const int draw = 2;
static const int player_x = 1;
static const int player_o = 2;
static const int window_size = 600;
static const int cell_size = 200;
static const int line_thick = 4;
static const int pad = 30;

uint8_t* make_board();
int board_line(uint8_t* b, int i, int j, int k);
int check_winner(uint8_t* b);
int board_full(uint8_t* b);
void draw_x(int col, int row, Color c);
void draw_o(int col, int row, Color c);
void draw_grid(Color c);
void draw_pieces(uint8_t* board, Color red, Color blue);
int main();

uint8_t* make_board() {
  size_t t2 = (size_t)9;
  void* t3 = malloc(t2);
  uint8_t* t4 = (uint8_t*)t3;
  uint8_t* p = t4;
  int i = 0;
  for (;;) {
    if (!((i < 9))) break;
    p[i] = 0;
    i = (i + 1);
  }
  return p;
}

int board_line(uint8_t* b, int i, int j, int k) {
  int t13;
  int t7;
  uint8_t t1 = b[i];
  uint8_t a = t1;
  if ((a != 0)) {
    uint8_t t8 = b[j];
    if ((a == t8)) {
      uint8_t t14 = b[k];
      t13 = (a == t14);
    } else {
      t13 = 0;
    }
    t7 = t13;
  } else {
    t7 = 0;
  }
  if (t7) {
    int t22 = (int)a;
    return t22;
  } else {
    return 0;
  }
}

int check_winner(uint8_t* b) {
  int r = 0;
  for (;;) {
    if (!((r < 3))) break;
    int t17 = board_line(b, (r * 3), ((r * 3) + 1), ((r * 3) + 2));
    int wr = t17;
    if ((wr != 0)) {
      return wr;
    } else {
    }
    r = (r + 1);
  }
  int c = 0;
  for (;;) {
    if (!((c < 3))) break;
    int t36 = board_line(b, c, (c + 3), (c + 6));
    int wc = t36;
    if ((wc != 0)) {
      return wc;
    } else {
    }
    c = (c + 1);
  }
  int t48 = board_line(b, 0, 4, 8);
  int wd1 = t48;
  if ((wd1 != 0)) {
    return wd1;
  } else {
  }
  int t58 = board_line(b, 2, 4, 6);
  int wd2 = t58;
  if ((wd2 != 0)) {
    return wd2;
  } else {
  }
  return 0;
}

int board_full(uint8_t* b) {
  int i = 0;
  for (;;) {
    if (!((i < 9))) break;
    uint8_t t10 = b[i];
    if ((t10 == 0)) {
      return 0;
    } else {
    }
    i = (i + 1);
  }
  return 1;
}

void draw_x(int col, int row, Color c) {
  int x1 = ((col * cell_size) + pad);
  int y1 = ((row * cell_size) + pad);
  int x2 = (((col + 1) * cell_size) - pad);
  int y2 = (((row + 1) * cell_size) - pad);
  float t13 = (float)x1;
  float t14 = (float)y1;
  Vector2 t15 = (Vector2){t13, t14};
  float t16 = (float)x2;
  float t17 = (float)y2;
  Vector2 t18 = (Vector2){t16, t17};
  float t19 = (float)line_thick;
  DrawLineEx(t15, t18, t19, c);
  float t21 = (float)x2;
  float t22 = (float)y1;
  Vector2 t23 = (Vector2){t21, t22};
  float t24 = (float)x1;
  float t25 = (float)y2;
  Vector2 t26 = (Vector2){t24, t25};
  float t27 = (float)line_thick;
  DrawLineEx(t23, t26, t27, c);
  return;
}

void draw_o(int col, int row, Color c) {
  int radius = ((cell_size / 2) - pad);
  int half = (line_thick / 2);
  float t14 = (float)((col * cell_size) + (cell_size / 2));
  float t15 = (float)((row * cell_size) + (cell_size / 2));
  Vector2 t16 = (Vector2){t14, t15};
  float t18 = (float)(radius - half);
  float t20 = (float)(radius + half);
  DrawRing(t16, t18, t20, 0.0, 360.0, 36, c);
  return;
}

void draw_grid(Color c) {
  int c1 = cell_size;
  int c2 = (cell_size * 2);
  float t3 = (float)c1;
  Vector2 t5 = (Vector2){t3, 0.0};
  float t6 = (float)c1;
  float t7 = (float)window_size;
  Vector2 t8 = (Vector2){t6, t7};
  float t9 = (float)line_thick;
  DrawLineEx(t5, t8, t9, c);
  float t11 = (float)c2;
  Vector2 t13 = (Vector2){t11, 0.0};
  float t14 = (float)c2;
  float t15 = (float)window_size;
  Vector2 t16 = (Vector2){t14, t15};
  float t17 = (float)line_thick;
  DrawLineEx(t13, t16, t17, c);
  float t20 = (float)c1;
  Vector2 t21 = (Vector2){0.0, t20};
  float t22 = (float)window_size;
  float t23 = (float)c1;
  Vector2 t24 = (Vector2){t22, t23};
  float t25 = (float)line_thick;
  DrawLineEx(t21, t24, t25, c);
  float t28 = (float)c2;
  Vector2 t29 = (Vector2){0.0, t28};
  float t30 = (float)window_size;
  float t31 = (float)c2;
  Vector2 t32 = (Vector2){t30, t31};
  float t33 = (float)line_thick;
  DrawLineEx(t29, t32, t33, c);
  return;
}

void draw_pieces(uint8_t* board, Color red, Color blue) {
  int i = 0;
  for (;;) {
    if (!((i < 9))) break;
    int col = (i % 3);
    int row = (i / 3);
    uint8_t t11 = board[i];
    uint8_t p = t11;
    if ((p == x_piece)) {
      draw_x(col, row, red);
    } else {
      if ((p == o_piece)) {
        draw_o(col, row, blue);
      } else {
      }
    }
    i = (i + 1);
  }
  return;
}

int main() {
  int t78;
  int t72;
  int t66;
  int t112;
  int t107;
  int t100;
  uint32_t t1 = (uint32_t)flag_msaa_4x;
  SetConfigFlags(t1);
  const char* t3 = "sysp-ir — Tic Tac Toe";
  InitWindow(window_size, window_size, t3);
  SetTargetFPS(60);
  uint8_t* t7 = make_board();
  uint8_t* board = t7;
  int turn = player_x;
  int state = playing;
  int winner = empty;
  Color t12 = (Color){245, 245, 245, 255};
  Color white = t12;
  Color t17 = (Color){0, 0, 0, 255};
  Color t22 = (Color){230, 41, 55, 255};
  Color red = t22;
  Color t27 = (Color){0, 121, 241, 255};
  Color blue = t27;
  Color t32 = (Color){0, 0, 0, 200};
  for (;;) {
    int t36 = WindowShouldClose();
    if (!((t36 == 0))) break;
    if ((state == playing)) {
      int t46 = IsMouseButtonPressed(mouse_left);
      if ((t46 != 0)) {
        Vector2 t49 = GetMousePosition();
        Vector2 mouse = t49;
        float t50 = mouse.x;
        float t51 = (float)cell_size;
        int t53 = (int)(t50 / t51);
        int col = t53;
        float t54 = mouse.y;
        float t55 = (float)cell_size;
        int t57 = (int)(t54 / t55);
        int row = t57;
        if ((col >= 0)) {
          if ((col < 3)) {
            if ((row >= 0)) {
              t78 = (row < 3);
            } else {
              t78 = 0;
            }
            t72 = t78;
          } else {
            t72 = 0;
          }
          t66 = t72;
        } else {
          t66 = 0;
        }
        if (t66) {
          int idx = ((row * 3) + col);
          uint8_t t90 = board[idx];
          if ((t90 == 0)) {
            uint8_t t93 = (uint8_t)turn;
            board[idx] = t93;
            int t94 = check_winner(board);
            winner = t94;
            if ((winner != 0)) {
              state = won;
              t100 = state;
            } else {
              int t101 = board_full(board);
              if ((t101 != 0)) {
                state = draw;
                t107 = state;
              } else {
                if ((turn == player_x)) {
                  t112 = player_o;
                } else {
                  t112 = player_x;
                }
                turn = t112;
                t107 = turn;
              }
              t100 = t107;
            }
          } else {
          }
        } else {
        }
      } else {
      }
    } else {
    }
    if ((state != playing)) {
      int t120 = IsMouseButtonPressed(mouse_left);
      if ((t120 != 0)) {
        int i = 0;
        for (;;) {
          if (!((i < 9))) break;
          board[i] = 0;
          i = (i + 1);
        }
        turn = player_x;
        state = playing;
        winner = 0;
      } else {
      }
    } else {
    }
    BeginDrawing();
    ClearBackground(t17);
    draw_grid(white);
    draw_pieces(board, red, blue);
    if ((state == playing)) {
      if ((turn == player_x)) {
        const char* t146 = "X's turn";
        DrawText(t146, 10, 570, 20, red);
      } else {
        const char* t151 = "O's turn";
        DrawText(t151, 10, 570, 20, blue);
      }
    } else {
    }
    if ((state != playing)) {
      DrawRectangle(0, 0, window_size, window_size, t32);
      if ((winner == x_piece)) {
        const char* t168 = "X Wins!";
        DrawText(t168, 180, 250, 60, red);
      } else {
        if ((winner == o_piece)) {
          const char* t178 = "O Wins!";
          DrawText(t178, 180, 250, 60, blue);
        } else {
          const char* t183 = "Draw!";
          DrawText(t183, 210, 250, 60, white);
        }
      }
      const char* t188 = "Click to play again";
      DrawText(t188, 150, 350, 30, white);
    } else {
    }
    EndDrawing();
  }
  void* t194 = (void*)board;
  free(t194);
  CloseWindow();
  return 0;
}

