# Matrix Screensaver for Linux
# Build: make
# Install: sudo make install
# Uninstall: sudo make uninstall
#
# Dependencies:
#   Debian/Ubuntu: sudo apt install libx11-dev libxft-dev
#   Arch Linux:    sudo pacman -S libx11 libxft

CC      ?= gcc
CFLAGS  ?= -O2 -Wall -Wextra
PREFIX  ?= /usr/local
BINDIR  ?= $(PREFIX)/bin
DATADIR ?= $(PREFIX)/share

PKG_CFLAGS  = $(shell pkg-config --cflags x11 xft 2>/dev/null)
PKG_LDFLAGS = $(shell pkg-config --libs x11 xft 2>/dev/null) -lm

TARGET = matrix-screensaver

.PHONY: all clean install uninstall

all: $(TARGET)

$(TARGET): matrix.c
	$(CC) $(CFLAGS) $(PKG_CFLAGS) -o $@ $< $(PKG_LDFLAGS)

clean:
	rm -f $(TARGET)

install: $(TARGET)
	install -Dm755 $(TARGET) $(DESTDIR)$(BINDIR)/$(TARGET)
	install -Dm644 matrix-screensaver.desktop $(DESTDIR)$(DATADIR)/applications/matrix-screensaver.desktop 2>/dev/null || true
	@echo ""
	@echo "Installed to $(DESTDIR)$(BINDIR)/$(TARGET)"
	@echo ""
	@echo "Usage:"
	@echo "  $(TARGET)              # Fullscreen"
	@echo "  $(TARGET) -window      # Windowed"
	@echo "  $(TARGET) -root        # XScreenSaver mode"
	@echo "  $(TARGET) -theme NAME  # Start with theme"
	@echo ""
	@echo "Available themes:"
	@echo "  classic megacity operator nightmare paradise"
	@echo "  resurrections trinity morpheus bugs"
	@echo "  palimpsest twilight neomatrixology rainbow"

uninstall:
	rm -f $(DESTDIR)$(BINDIR)/$(TARGET)
	rm -f $(DESTDIR)$(DATADIR)/applications/matrix-screensaver.desktop
