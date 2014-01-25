CPPFLAGS=-I../include
CFLAGS=-m32 -O2 -pipe -Wall -Wno-unused-function -D__target_arm__
TOOLS=iboot_patcher kernel_patcher
IBOOT_PATCHER_OBJECTS=ibootsup.o patch.o util.o iboot_patcher.o
KERNEL_PATCHER_OBJECTS=patch.o util.o kcache.o macho_loader.o kernel_patcher.o

all: $(TOOLS)

iboot_patcher: $(IBOOT_PATCHER_OBJECTS)
	$(CC) $(CFLAGS) $(IBOOT_PATCHER_OBJECTS) -o $@

kernel_patcher: $(KERNEL_PATCHER_OBJECTS)
	$(CC) $(CFLAGS) $(KERNEL_PATCHER_OBJECTS) -o $@

%.o: %.c
	$(CC) $(CFLAGS) $(CPPFLAGS) -c -o $@ $<

clean:
	rm -f $(TOOLS) *.o
