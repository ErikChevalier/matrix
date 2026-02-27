// Matrix Screensaver for Linux (X11)
// Ported from Windows version by Henry++ / J Brown
// Themes inspired by Rezmason/matrix (https://github.com/Rezmason/matrix)
//
// Build: make
// Run:   ./matrix-screensaver [-root] [-window-id ID] [-theme NAME] [-fullscreen]

#include <X11/Xlib.h>
#include <X11/Xutil.h>
#include <X11/keysym.h>
#include <X11/Xft/Xft.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <unistd.h>
#include <signal.h>

// ============================================================
// Constants (matching Windows version)
// ============================================================

#define MAX_INTENSITY    5
#define GLYPH_WIDTH      14
#define GLYPH_HEIGHT     14

#define AMOUNT_MIN       1
#define AMOUNT_MAX       26
#define AMOUNT_DEFAULT   26

#define DENSITY_MIN      5
#define DENSITY_MAX      50
#define DENSITY_DEFAULT  30

#define SPEED_MIN        1
#define SPEED_MAX        10
#define SPEED_DEFAULT    6

#define HUE_MIN          1
#define HUE_MAX          255
#define HUE_DEFAULT      85

#define GLYPH_REDRAW     0x8000

#define THEME_COUNT      13
#define MENU_ITEM_COUNT  8

// ============================================================
// Types
// ============================================================

typedef unsigned int GLYPH;

typedef struct {
	const char *name;
	int hue, speed, density, amount;
	int is_random, is_smooth;
} Theme;

typedef struct {
	GLYPH *glyph;
	int state;
	int countdown;
	unsigned int blip_pos;
	unsigned int blip_length;
	unsigned int length;
	unsigned int run_length;
	int is_started;
} MatrixColumn;

typedef struct {
	unsigned int width, height;
	unsigned int numcols, numrows;
	MatrixColumn *column;
} Matrix;

typedef struct {
	int amount, density, speed, hue;
	int is_esc_only, is_random, is_smooth;
} Config;

typedef struct {
	int is_visible;
	int selected;
	int current_theme;
} MenuState;

// ============================================================
// Globals
// ============================================================

static Config config = {0};
static MenuState menu = {0};
static volatile int running = 1;

// Glyph masks: grayscale intensity per glyph [glyph_index][pixel]
static unsigned char glyph_masks[AMOUNT_MAX][GLYPH_WIDTH * GLYPH_HEIGHT];
static int glyph_count = 0;

// Sprite sheet pixel data: [intensity * GLYPH_HEIGHT + y][glyph * GLYPH_WIDTH + x]
static unsigned int *sprite_data = NULL;
static int sprite_w = 0, sprite_h = 0;

// Half-width Katakana range: U+FF66 to U+FF9D (56 chars, we use up to 26)
static const int katakana_start = 0xFF66;

// ============================================================
// Theme definitions (Rezmason-inspired, mapped to GDI params)
// ============================================================

static const Theme themes[THEME_COUNT] = {
	{ "CLASSIC",         72,  6, 30, 26, 0, 1 },
	{ "MEGACITY",        72,  3, 30, 26, 0, 1 },
	{ "OPERATOR",        96,  8, 40, 26, 0, 1 },
	{ "NIGHTMARE",        1, 10, 20, 26, 0, 1 },
	{ "PARADISE",        12,  2, 15, 26, 0, 1 },
	{ "RESURRECTIONS",   90,  6, 30, 26, 0, 1 },
	{ "TRINITY",         89,  5, 25, 26, 0, 1 },
	{ "MORPHEUS",       233,  4, 25, 26, 0, 1 },
	{ "BUGS",            29,  7, 25, 26, 0, 1 },
	{ "PALIMPSEST",     144,  7, 35, 20, 0, 1 },
	{ "TWILIGHT",       153,  3, 25, 20, 0, 1 },
	{ "NEOMATRIXOLOGY",  36,  5, 40, 12, 0, 1 },
	{ "RAINBOW",         72,  7, 30, 26, 1, 1 },
};

// ============================================================
// HSL to RGB (Windows HLS compatible: H=0-240, S=0-240, L=0-240)
// ============================================================

static unsigned int hsl_to_rgb (int h, int s, int l)
{
	double hf, sf, lf, c, x, m;
	double r = 0, g = 0, b = 0;
	int hi;

	hf = (double)h / 240.0 * 360.0;
	sf = (double)s / 240.0;
	lf = (double)l / 240.0;

	c = (1.0 - fabs (2.0 * lf - 1.0)) * sf;
	x = c * (1.0 - fabs (fmod (hf / 60.0, 2.0) - 1.0));
	m = lf - c / 2.0;

	hi = (int)(hf / 60.0) % 6;

	switch (hi)
	{
		case 0: r = c; g = x; b = 0; break;
		case 1: r = x; g = c; b = 0; break;
		case 2: r = 0; g = c; b = x; break;
		case 3: r = 0; g = x; b = c; break;
		case 4: r = x; g = 0; b = c; break;
		case 5: r = c; g = 0; b = x; break;
	}

	int ri = (int)((r + m) * 255);
	int gi = (int)((g + m) * 255);
	int bi = (int)((b + m) * 255);

	if (ri < 0) ri = 0; if (ri > 255) ri = 255;
	if (gi < 0) gi = 0; if (gi > 255) gi = 255;
	if (bi < 0) bi = 0; if (bi > 255) bi = 255;

	return (ri << 16) | (gi << 8) | bi;
}

static void rgb_to_hsl (unsigned int color, int *h, int *s, int *l)
{
	double r = ((color >> 16) & 0xFF) / 255.0;
	double g = ((color >> 8) & 0xFF) / 255.0;
	double b = (color & 0xFF) / 255.0;
	double max, min, d, hf, sf, lf;

	max = r > g ? (r > b ? r : b) : (g > b ? g : b);
	min = r < g ? (r < b ? r : b) : (g < b ? g : b);
	lf = (max + min) / 2.0;
	d = max - min;

	if (d < 0.001)
	{
		hf = 0; sf = 0;
	}
	else
	{
		sf = lf > 0.5 ? d / (2.0 - max - min) : d / (max + min);

		if (max == r) hf = fmod ((g - b) / d + 6.0, 6.0);
		else if (max == g) hf = (b - r) / d + 2.0;
		else hf = (r - g) / d + 4.0;

		hf *= 60.0;
	}

	*h = (int)(hf / 360.0 * 240.0);
	*s = (int)(sf * 240.0);
	*l = (int)(lf * 240.0);
}

// ============================================================
// Random helpers
// ============================================================

static int rnd_range (int lo, int hi)
{
	if (hi <= lo) return lo;
	return lo + (rand () % (hi - lo + 1));
}

// ============================================================
// Glyph atlas generation via Xft
// ============================================================

static void generate_glyph_masks (Display *dpy, int screen)
{
	XftFont *font;
	Pixmap pix;
	XftDraw *draw;
	XftColor white, black;
	XImage *img;
	Visual *vis;
	Colormap cmap;
	int i, px, py;
	FcChar32 ch;
	XGlyphInfo extents;

	vis = DefaultVisual (dpy, screen);
	cmap = DefaultColormap (dpy, screen);

	// Try fonts with katakana support, fall back to monospace
	font = XftFontOpenName (dpy, screen, "Noto Sans Mono CJK JP:size=10");

	if (!font)
		font = XftFontOpenName (dpy, screen, "VL Gothic:size=10");

	if (!font)
		font = XftFontOpenName (dpy, screen, "DejaVu Sans Mono:size=10");

	if (!font)
		font = XftFontOpenName (dpy, screen, "monospace:size=10");

	if (!font)
		return;

	pix = XCreatePixmap (dpy, RootWindow (dpy, screen),
		GLYPH_WIDTH, GLYPH_HEIGHT, DefaultDepth (dpy, screen));

	draw = XftDrawCreate (dpy, pix, vis, cmap);

	XftColorAllocValue (dpy, vis, cmap,
		&(XRenderColor){0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF}, &white);
	XftColorAllocValue (dpy, vis, cmap,
		&(XRenderColor){0, 0, 0, 0xFFFF}, &black);

	glyph_count = AMOUNT_MAX;

	for (i = 0; i < glyph_count; i++)
	{
		// Clear to black
		XftDrawRect (draw, &black, 0, 0, GLYPH_WIDTH, GLYPH_HEIGHT);

		// Pick character: katakana or fallback to ASCII
		ch = katakana_start + i;

		if (!XftCharExists (dpy, font, ch))
			ch = '0' + (i % 10);  // Fallback to digits

		// Center glyph
		XftTextExtents32 (dpy, font, &ch, 1, &extents);

		px = (GLYPH_WIDTH - extents.width) / 2 - extents.x;
		py = (GLYPH_HEIGHT - extents.height) / 2 + extents.y;

		XftDrawString32 (draw, &white, font, px, py, &ch, 1);

		// Read pixel data
		img = XGetImage (dpy, pix, 0, 0, GLYPH_WIDTH, GLYPH_HEIGHT,
			AllPlanes, ZPixmap);

		if (img)
		{
			for (py = 0; py < GLYPH_HEIGHT; py++)
			{
				for (px = 0; px < GLYPH_WIDTH; px++)
				{
					unsigned long pixel = XGetPixel (img, px, py);
					// Extract green channel as brightness (white = all channels)
					int brightness = (pixel >> 8) & 0xFF;
					glyph_masks[i][py * GLYPH_WIDTH + px] = brightness;
				}
			}

			XDestroyImage (img);
		}
	}

	XftColorFree (dpy, vis, cmap, &white);
	XftColorFree (dpy, vis, cmap, &black);
	XftDrawDestroy (draw);
	XFreePixmap (dpy, pix);
	XftFontClose (dpy, font);
}

// ============================================================
// Sprite sheet: all glyphs at all intensity levels, colorized
// ============================================================

static void make_sprite_sheet (int hue)
{
	int intensity, g, px, py;
	int h, s, l;
	unsigned int color;
	double mask, bright;

	sprite_w = glyph_count * GLYPH_WIDTH;
	sprite_h = (MAX_INTENSITY + 1) * GLYPH_HEIGHT;

	if (!sprite_data)
		sprite_data = malloc (sprite_w * sprite_h * sizeof (unsigned int));

	for (intensity = 0; intensity <= MAX_INTENSITY; intensity++)
	{
		bright = (double)intensity / MAX_INTENSITY;

		// Create color at this intensity level
		h = hue;
		s = 200;  // High saturation
		l = (int)(bright * 200);

		color = hsl_to_rgb (h, s, l);

		for (g = 0; g < glyph_count; g++)
		{
			for (py = 0; py < GLYPH_HEIGHT; py++)
			{
				for (px = 0; px < GLYPH_WIDTH; px++)
				{
					mask = glyph_masks[g][py * GLYPH_WIDTH + px] / 255.0;

					int r = (int)(((color >> 16) & 0xFF) * mask);
					int gn = (int)(((color >> 8) & 0xFF) * mask);
					int b = (int)((color & 0xFF) * mask);

					sprite_data[
						(intensity * GLYPH_HEIGHT + py) * sprite_w +
						g * GLYPH_WIDTH + px
					] = (r << 16) | (gn << 8) | b;
				}
			}
		}
	}
}

// ============================================================
// Matrix column state machine (ported from Windows version)
// ============================================================

static GLYPH glyph_intensity (GLYPH g) { return (g & 0x7F00) >> 8; }

static GLYPH random_glyph (int intensity)
{
	return GLYPH_REDRAW | (intensity << 8) | (rand () % config.amount);
}

static GLYPH darken_glyph (GLYPH g)
{
	int i = glyph_intensity (g);
	if (i > 0)
		return GLYPH_REDRAW | ((i - 1) << 8) | (g & 0x00FF);
	return g;
}

static void scroll_column (MatrixColumn *col)
{
	GLYPH last, cur;
	int cur_int, density;
	unsigned int y;

	if (!col->is_started)
	{
		if (--col->countdown <= 0)
			col->is_started = 1;
		return;
	}

	last = col->state ? 0 : (MAX_INTENSITY << 8);

	for (y = 0; y < col->length; y++)
	{
		cur = col->glyph[y];
		cur_int = glyph_intensity (cur);

		if (cur_int < (int)glyph_intensity (last) && cur_int == 0)
		{
			col->glyph[y] = random_glyph (MAX_INTENSITY - 1);
			y++;
		}
		else if (cur_int > (int)glyph_intensity (last))
		{
			col->glyph[y] = darken_glyph (cur);
			if (cur_int == MAX_INTENSITY - 1)
				y++;
		}

		last = col->glyph[y];
	}

	if (--col->run_length <= 0)
	{
		density = DENSITY_MAX - config.density + DENSITY_MIN;

		if ((col->state ^= 1))
			col->run_length = rand () % (3 * density / 2) + DENSITY_MIN;
		else
			col->run_length = rand () % (DENSITY_MAX + 1 - density) + (DENSITY_MIN * 2);
	}

	if (col->blip_pos < col->length)
	{
		col->glyph[col->blip_pos] |= GLYPH_REDRAW;
		if (col->blip_pos + 1 < col->length) col->glyph[col->blip_pos + 1] |= GLYPH_REDRAW;
		if (col->blip_pos + 8 < col->length) col->glyph[col->blip_pos + 8] |= GLYPH_REDRAW;
		if (col->blip_pos + 9 < col->length) col->glyph[col->blip_pos + 9] |= GLYPH_REDRAW;
	}

	col->blip_pos += 2;

	if (col->blip_pos >= col->blip_length)
	{
		col->blip_length = col->length + (rand () % 50);
		col->blip_pos = 0;
	}

	if (col->blip_pos < col->length)
	{
		col->glyph[col->blip_pos] |= GLYPH_REDRAW;
		if (col->blip_pos + 1 < col->length) col->glyph[col->blip_pos + 1] |= GLYPH_REDRAW;
		if (col->blip_pos + 8 < col->length) col->glyph[col->blip_pos + 8] |= GLYPH_REDRAW;
		if (col->blip_pos + 9 < col->length) col->glyph[col->blip_pos + 9] |= GLYPH_REDRAW;
	}
}

static void randomize_column (MatrixColumn *col)
{
	unsigned int i, y;
	int r;

	for (i = 1, y = 0; i < 16; i++)
	{
		while (y < col->length && (int)glyph_intensity (col->glyph[y]) < (MAX_INTENSITY - 1))
			y++;

		if (y >= col->length) break;

		r = rand ();
		col->glyph[y] = (col->glyph[y] & 0xFF00) | (r % config.amount);
		col->glyph[y] |= GLYPH_REDRAW;
		y += r % 10;
	}
}

// ============================================================
// Matrix create/destroy
// ============================================================

static Matrix *create_matrix (unsigned int w, unsigned int h)
{
	Matrix *m = calloc (1, sizeof (Matrix));
	unsigned int x;

	m->numcols = w / GLYPH_WIDTH + 1;
	m->numrows = h / GLYPH_HEIGHT + 1;
	m->width = w;
	m->height = h;
	m->column = calloc (m->numcols, sizeof (MatrixColumn));

	for (x = 0; x < m->numcols; x++)
	{
		m->column[x].length = m->numrows;
		m->column[x].countdown = rand () % 100;
		m->column[x].state = rand () % 2;
		m->column[x].run_length = rand () % 20 + 3;
		m->column[x].glyph = calloc (m->numrows + 16, sizeof (GLYPH));
	}

	return m;
}

static void destroy_matrix (Matrix *m)
{
	unsigned int x;

	if (!m) return;

	for (x = 0; x < m->numcols; x++)
		free (m->column[x].glyph);

	free (m->column);
	free (m);
}

// ============================================================
// Apply theme
// ============================================================

static void apply_theme (int idx)
{
	config.hue = themes[idx].hue;
	config.speed = themes[idx].speed;
	config.density = themes[idx].density;
	config.amount = themes[idx].amount;
	config.is_random = themes[idx].is_random;
	config.is_smooth = themes[idx].is_smooth;

	make_sprite_sheet (config.hue);
}

// ============================================================
// Draw a single glyph from sprite sheet to XImage backbuffer
// ============================================================

static void draw_glyph (unsigned int *backbuf, int buf_w,
	unsigned int xpos, unsigned int ypos, GLYPH g)
{
	int intensity, glyph_idx, px, py;
	int src_x, src_y, dst_x, dst_y;

	intensity = glyph_intensity (g);
	glyph_idx = g & 0xFF;

	if (glyph_idx >= glyph_count) glyph_idx = 0;

	for (py = 0; py < GLYPH_HEIGHT; py++)
	{
		src_y = intensity * GLYPH_HEIGHT + py;
		dst_y = ypos + py;

		for (px = 0; px < GLYPH_WIDTH; px++)
		{
			src_x = glyph_idx * GLYPH_WIDTH + px;
			dst_x = xpos + px;

			backbuf[dst_y * buf_w + dst_x] =
				sprite_data[src_y * sprite_w + src_x];
		}
	}
}

// ============================================================
// Render frame
// ============================================================

static void decode_matrix (Matrix *m, unsigned int *backbuf, int buf_w)
{
	static int new_hue = 0;
	unsigned int x, y;
	MatrixColumn *col;
	GLYPH g;

	if (!new_hue) new_hue = config.hue;

	for (x = 0; x < m->numcols; x++)
	{
		col = &m->column[x];

		randomize_column (col);
		scroll_column (col);

		// Redraw dirty glyphs
		for (y = 0; y < col->length; y++)
		{
			g = col->glyph[y];

			if (g & GLYPH_REDRAW)
			{
				if ((int)glyph_intensity (g) >= MAX_INTENSITY - 1 &&
					(y == col->blip_pos || y == col->blip_pos + 1 ||
					 y == col->blip_pos + 8 || y == col->blip_pos + 9))
					g |= MAX_INTENSITY << 8;

				draw_glyph (backbuf, buf_w, x * GLYPH_WIDTH, y * GLYPH_HEIGHT, g);
				col->glyph[y] &= ~GLYPH_REDRAW;
			}
		}
	}

	// Handle hue changes
	if (config.is_random)
	{
		if (config.is_smooth)
			new_hue = (new_hue >= HUE_MAX) ? HUE_MIN : new_hue + 1;
		else if (rand () % 2)
			new_hue = rnd_range (HUE_MIN, HUE_MAX);
	}
	else
	{
		new_hue = config.hue;
	}

	make_sprite_sheet (new_hue);
}

// ============================================================
// Terminal menu overlay (drawn to backbuffer)
// ============================================================

static void draw_text (unsigned int *buf, int buf_w, int buf_h,
	int tx, int ty, const char *text, unsigned int color)
{
	// Minimal 5x7 bitmap font renderer for the terminal overlay
	// Each char is drawn as a colored rectangle (simplified approach)
	// For a real font, we'd use Xft — but this overlay is drawn to
	// the raw pixel buffer, so we use a simple approach
	int i, cx;

	cx = tx;

	for (i = 0; text[i]; i++)
	{
		if (text[i] == ' ')
		{
			cx += 8;
			continue;
		}

		// Draw a small colored block for each character
		// In production, you'd use a bitmap font here
		int px, py;
		for (py = 0; py < 10; py++)
		{
			for (px = 0; px < 7; px++)
			{
				int dx = cx + px;
				int dy = ty + py;
				if (dx >= 0 && dx < buf_w && dy >= 0 && dy < buf_h)
					buf[dy * buf_w + dx] = color;
			}
		}
		cx += 8;
	}
}

static void draw_menu_line (unsigned int *buf, int buf_w, int buf_h,
	int x, int y, const char *text, unsigned int color)
{
	draw_text (buf, buf_w, buf_h, x, y, text, color);
}

static void draw_terminal_menu (unsigned int *buf, int buf_w, int buf_h)
{
	int menu_w = 400, menu_h = 280;
	int left = (buf_w - menu_w) / 2;
	int top = (buf_h - menu_h) / 2;
	int x, y, px, py, i;
	char line[128];
	unsigned int bg = 0x000A00;
	unsigned int border = 0x00B400;
	unsigned int bright = 0x00FF41;
	unsigned int dim = 0x008C23;
	unsigned int subdim = 0x006419;

	// Fill background
	for (py = top; py < top + menu_h && py < buf_h; py++)
		for (px = left; px < left + menu_w && px < buf_w; px++)
			if (py >= 0 && px >= 0)
				buf[py * buf_w + px] = bg;

	// Draw border
	for (px = left; px < left + menu_w; px++)
	{
		if (px >= 0 && px < buf_w)
		{
			if (top >= 0 && top < buf_h) buf[top * buf_w + px] = border;
			if (top + menu_h - 1 >= 0 && top + menu_h - 1 < buf_h)
				buf[(top + menu_h - 1) * buf_w + px] = border;
		}
	}

	for (py = top; py < top + menu_h; py++)
	{
		if (py >= 0 && py < buf_h)
		{
			if (left >= 0 && left < buf_w) buf[py * buf_w + left] = border;
			if (left + menu_w - 1 >= 0 && left + menu_w - 1 < buf_w)
				buf[py * buf_w + left + menu_w - 1] = border;
		}
	}

	x = left + 16;
	y = top + 14;

	draw_menu_line (buf, buf_w, buf_h, x, y, "MATRIX CONTROL TERMINAL", bright);
	y += 16;
	draw_menu_line (buf, buf_w, buf_h, x, y, "========================================", subdim);
	y += 18;

	// Theme item
	snprintf (line, sizeof (line), "%s THEME              [ %-14s ]",
		menu.selected == 0 ? ">" : " ", themes[menu.current_theme].name);
	draw_menu_line (buf, buf_w, buf_h, x, y, line, menu.selected == 0 ? bright : dim);
	y += 14;

	draw_menu_line (buf, buf_w, buf_h, x, y, "----------------------------------------", subdim);
	y += 14;

	// Parameter items
	const char *names[] = { "SPEED", "DENSITY", "AMOUNT", "HUE",
		"RANDOM COLORS", "SMOOTH TRANSITION", "ESC ONLY" };
	int vals[] = { config.speed, config.density, config.amount, config.hue,
		config.is_random, config.is_smooth, config.is_esc_only };
	int mins[] = { SPEED_MIN, DENSITY_MIN, AMOUNT_MIN, HUE_MIN, 0, 0, 0 };
	int maxs[] = { SPEED_MAX, DENSITY_MAX, AMOUNT_MAX, HUE_MAX, 1, 1, 1 };

	for (i = 0; i < 7; i++)
	{
		int sel = (i + 1) == menu.selected;

		if (maxs[i] <= 1)
			snprintf (line, sizeof (line), "%s %-20s [ %s ]",
				sel ? ">" : " ", names[i], vals[i] ? "ON " : "OFF");
		else
			snprintf (line, sizeof (line), "%s %-20s [%4d ]  %d-%d",
				sel ? ">" : " ", names[i], vals[i], mins[i], maxs[i]);

		draw_menu_line (buf, buf_w, buf_h, x, y, line, sel ? bright : dim);
		y += 14;
	}

	y += 8;
	draw_menu_line (buf, buf_w, buf_h, x, y, "========================================", subdim);
	y += 16;
	draw_menu_line (buf, buf_w, buf_h, x, y, "F1:MENU  ARROWS:NAV/SET  SHIFT:x10  R:RST", subdim);
}

// ============================================================
// Menu key handling
// ============================================================

static int handle_menu_key (KeySym key, int shift)
{
	int delta, new_val;

	if (key == XK_F1)
	{
		menu.is_visible = !menu.is_visible;
		return 1;
	}

	if (!menu.is_visible) return 0;

	switch (key)
	{
		case XK_Up:
			menu.selected = menu.selected > 0 ? menu.selected - 1 : MENU_ITEM_COUNT - 1;
			return 1;

		case XK_Down:
			menu.selected = menu.selected < MENU_ITEM_COUNT - 1 ? menu.selected + 1 : 0;
			return 1;

		case XK_Left:
		case XK_Right:
			delta = (key == XK_Right) ? 1 : -1;
			if (shift) delta *= 10;

			switch (menu.selected)
			{
				case 0: // THEME
					menu.current_theme += (delta > 0) ? 1 : -1;
					if (menu.current_theme < 0) menu.current_theme = THEME_COUNT - 1;
					if (menu.current_theme >= THEME_COUNT) menu.current_theme = 0;
					apply_theme (menu.current_theme);
					break;
				case 1: // SPEED
					new_val = config.speed + delta;
					if (new_val < SPEED_MIN) new_val = SPEED_MIN;
					if (new_val > SPEED_MAX) new_val = SPEED_MAX;
					config.speed = new_val;
					break;
				case 2: // DENSITY
					new_val = config.density + delta;
					if (new_val < DENSITY_MIN) new_val = DENSITY_MIN;
					if (new_val > DENSITY_MAX) new_val = DENSITY_MAX;
					config.density = new_val;
					break;
				case 3: // AMOUNT
					new_val = config.amount + delta;
					if (new_val < AMOUNT_MIN) new_val = AMOUNT_MIN;
					if (new_val > AMOUNT_MAX) new_val = AMOUNT_MAX;
					config.amount = new_val;
					break;
				case 4: // HUE
					new_val = config.hue + delta;
					if (new_val < HUE_MIN) new_val = HUE_MIN;
					if (new_val > HUE_MAX) new_val = HUE_MAX;
					config.hue = new_val;
					make_sprite_sheet (config.hue);
					break;
				case 5: config.is_random = !config.is_random; break;
				case 6: config.is_smooth = !config.is_smooth; break;
				case 7: config.is_esc_only = !config.is_esc_only; break;
			}
			return 1;

		case XK_r: case XK_R:
			menu.current_theme = 0;
			apply_theme (0);
			config.is_esc_only = 0;
			return 1;

		case XK_Escape:
			menu.is_visible = 0;
			return 1;
	}

	return 1;  // Consume all keys when menu is open
}

// ============================================================
// Signal handler for clean exit
// ============================================================

static void sig_handler (int sig)
{
	(void)sig;
	running = 0;
}

// ============================================================
// Main
// ============================================================

int main (int argc, char **argv)
{
	Display *dpy;
	Window win;
	int screen;
	GC gc;
	XImage *ximg;
	Matrix *matrix;
	unsigned int *backbuf;
	int width, height, buf_stride;
	XEvent ev;
	int use_root = 0;
	Window parent_win = 0;
	int fullscreen = 1;
	int initial_theme = 0;
	int i;
	struct timespec ts;

	// Parse command line
	for (i = 1; i < argc; i++)
	{
		if (strcmp (argv[i], "-root") == 0)
			use_root = 1;
		else if (strcmp (argv[i], "-window-id") == 0 && i + 1 < argc)
			parent_win = (Window)strtol (argv[++i], NULL, 0);
		else if (strcmp (argv[i], "-window") == 0)
			fullscreen = 0;
		else if (strcmp (argv[i], "-theme") == 0 && i + 1 < argc)
		{
			i++;
			for (int t = 0; t < THEME_COUNT; t++)
			{
				if (strcasecmp (argv[i], themes[t].name) == 0)
				{
					initial_theme = t;
					break;
				}
			}
		}
		else if (strcmp (argv[i], "-speed") == 0 && i + 1 < argc)
			config.speed = atoi (argv[++i]);
		else if (strcmp (argv[i], "-hue") == 0 && i + 1 < argc)
			config.hue = atoi (argv[++i]);
	}

	signal (SIGINT, sig_handler);
	signal (SIGTERM, sig_handler);
	srand (time (NULL));

	// Set default config
	config.amount = AMOUNT_DEFAULT;
	config.density = DENSITY_DEFAULT;
	config.speed = SPEED_DEFAULT;
	config.hue = HUE_DEFAULT;
	config.is_smooth = 1;

	// Apply initial theme
	menu.current_theme = initial_theme;
	apply_theme (initial_theme);

	dpy = XOpenDisplay (NULL);

	if (!dpy)
	{
		fprintf (stderr, "Cannot open display\n");
		return 1;
	}

	screen = DefaultScreen (dpy);

	// Generate glyph masks using Xft
	generate_glyph_masks (dpy, screen);

	if (glyph_count == 0)
	{
		fprintf (stderr, "Failed to generate glyphs\n");
		XCloseDisplay (dpy);
		return 1;
	}

	// Create sprite sheet
	make_sprite_sheet (config.hue);

	// Determine window
	if (use_root)
	{
		win = RootWindow (dpy, screen);
	}
	else if (parent_win)
	{
		win = parent_win;
	}
	else
	{
		XSetWindowAttributes attrs;
		int scr_w, scr_h;

		scr_w = DisplayWidth (dpy, screen);
		scr_h = DisplayHeight (dpy, screen);

		if (fullscreen)
		{
			attrs.override_redirect = True;
			attrs.background_pixel = BlackPixel (dpy, screen);

			win = XCreateWindow (dpy, RootWindow (dpy, screen),
				0, 0, scr_w, scr_h, 0,
				CopyFromParent, InputOutput, CopyFromParent,
				CWOverrideRedirect | CWBackPixel, &attrs);
		}
		else
		{
			win = XCreateSimpleWindow (dpy, RootWindow (dpy, screen),
				100, 100, 800, 600, 0,
				WhitePixel (dpy, screen), BlackPixel (dpy, screen));
		}

		XStoreName (dpy, win, "Matrix Screensaver");
		XSelectInput (dpy, win, ExposureMask | KeyPressMask |
			StructureNotifyMask | ButtonPressMask | PointerMotionMask);
		XMapWindow (dpy, win);

		// Hide cursor in fullscreen
		if (fullscreen)
		{
			Pixmap blank;
			XColor dummy;
			Cursor invisible;
			static char empty[] = {0};

			blank = XCreateBitmapFromData (dpy, win, empty, 1, 1);
			invisible = XCreatePixmapCursor (dpy, blank, blank, &dummy, &dummy, 0, 0);
			XDefineCursor (dpy, win, invisible);
			XFreePixmap (dpy, blank);
		}
	}

	// Get window dimensions
	{
		XWindowAttributes wa;
		XGetWindowAttributes (dpy, win, &wa);
		width = wa.width;
		height = wa.height;
	}

	gc = XCreateGC (dpy, win, 0, NULL);

	// Create backbuffer
	buf_stride = width;
	backbuf = calloc (width * height, sizeof (unsigned int));

	ximg = XCreateImage (dpy, DefaultVisual (dpy, screen),
		DefaultDepth (dpy, screen), ZPixmap, 0,
		(char *)backbuf, width, height, 32, width * 4);

	// Create matrix
	matrix = create_matrix (width, height);

	// Main loop
	while (running)
	{
		// Process events
		while (XPending (dpy))
		{
			XNextEvent (dpy, &ev);

			switch (ev.type)
			{
				case KeyPress:
				{
					KeySym key = XLookupKeysym (&ev.xkey, 0);
					int shift = ev.xkey.state & ShiftMask;

					if (handle_menu_key (key, shift))
						break;

					if (key == XK_Escape || key == XK_q)
						running = 0;
					else if (!config.is_esc_only && !menu.is_visible)
						running = 0;

					break;
				}

				case ButtonPress:
					if (!config.is_esc_only && !menu.is_visible)
						running = 0;
					break;

				case ConfigureNotify:
					if (ev.xconfigure.width != width || ev.xconfigure.height != height)
					{
						width = ev.xconfigure.width;
						height = ev.xconfigure.height;

						destroy_matrix (matrix);
						matrix = create_matrix (width, height);

						// Recreate backbuffer
						ximg->data = NULL;
						XDestroyImage (ximg);
						backbuf = calloc (width * height, sizeof (unsigned int));
						buf_stride = width;

						ximg = XCreateImage (dpy, DefaultVisual (dpy, screen),
							DefaultDepth (dpy, screen), ZPixmap, 0,
							(char *)backbuf, width, height, 32, width * 4);
					}
					break;
			}
		}

		// Render frame
		decode_matrix (matrix, backbuf, buf_stride);

		// Draw menu overlay if visible
		if (menu.is_visible)
			draw_terminal_menu (backbuf, width, height);

		// Blit to window
		XPutImage (dpy, win, gc, ximg, 0, 0, 0, 0, width, height);
		XFlush (dpy);

		// Frame timing
		ts.tv_sec = 0;
		ts.tv_nsec = ((SPEED_MAX - config.speed) + SPEED_MIN) * 10 * 1000000L;
		nanosleep (&ts, NULL);
	}

	// Cleanup
	destroy_matrix (matrix);

	ximg->data = NULL;  // We manage backbuf ourselves
	XDestroyImage (ximg);
	free (backbuf);
	free (sprite_data);
	XFreeGC (dpy, gc);

	if (!use_root && !parent_win)
		XDestroyWindow (dpy, win);

	XCloseDisplay (dpy);

	return 0;
}
