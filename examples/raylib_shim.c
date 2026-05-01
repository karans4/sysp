/* Thin shim around raylib that hides Vector2 / Color (passed-by-value
 * structs) behind plain int / uint8_t args. Lets sysp-ir bind raylib
 * via simple extern declarations. */

#include <raylib.h>
#include <stdint.h>

void rl_init(int w, int h, const char* title) { InitWindow(w, h, title); }
void rl_close(void) { CloseWindow(); }
int  rl_should_close(void) { return WindowShouldClose(); }
void rl_set_fps(int n) { SetTargetFPS(n); }
void rl_set_msaa(void) { SetConfigFlags(FLAG_MSAA_4X_HINT); }

int rl_left_click_pressed(void) { return IsMouseButtonPressed(MOUSE_BUTTON_LEFT); }
int rl_mouse_x(void) { return (int)GetMousePosition().x; }
int rl_mouse_y(void) { return (int)GetMousePosition().y; }

void rl_begin(void) { BeginDrawing(); }
void rl_end(void)   { EndDrawing(); }

void rl_clear(uint8_t r, uint8_t g, uint8_t b, uint8_t a) {
    ClearBackground((Color){r, g, b, a});
}

void rl_line(int x1, int y1, int x2, int y2, int thick,
             uint8_t r, uint8_t g, uint8_t b, uint8_t a) {
    DrawLineEx((Vector2){(float)x1, (float)y1},
               (Vector2){(float)x2, (float)y2},
               (float)thick,
               (Color){r, g, b, a});
}

void rl_ring(int cx, int cy, int ri, int ro,
             uint8_t r, uint8_t g, uint8_t b, uint8_t a) {
    DrawRing((Vector2){(float)cx, (float)cy},
             (float)ri, (float)ro, 0.0f, 360.0f, 36,
             (Color){r, g, b, a});
}

void rl_rect(int x, int y, int w, int h,
             uint8_t r, uint8_t g, uint8_t b, uint8_t a) {
    DrawRectangle(x, y, w, h, (Color){r, g, b, a});
}

void rl_text(const char* s, int x, int y, int sz,
             uint8_t r, uint8_t g, uint8_t b, uint8_t a) {
    DrawText(s, x, y, sz, (Color){r, g, b, a});
}
