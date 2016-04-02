# For build instructions, see picosshd.c.

CC ?= gcc
CFLAGS += -pthread
CFLAGS += -Wall
CFLAGS += -g
SRC ?= picosshd.c
OUTPUT = picosshd
LIBS=lib/sockets.c lib/stringBuffers.c lib/zout.c skipthis.c lib/threading.c
CFILES += $(LIBS) $(SRC)
CFLAGS += $(shell pkg-config --cflags libsodium)
LFLAGS += $(shell pkg-config --libs libsodium)

default: build
.PHONY: default

# Eclipse likes the target "all".
all: build
.PHONY: all

%.o: %.c %.h
	$(CC) -o $*.o -c $(CFLAGS) $*.c

build: $(OUTPUT)
.PHONY: build

$(OUTPUT): $(addsuffix .o, $(basename $(CFILES)))
	$(CC) -o $(OUTPUT) $(CFLAGS) $(addsuffix .o, $(basename $(CFILES))) $(LFLAGS)

verify:
	verifast -emit_vfmanifest -c lib/stringBuffers.c
	verifast -prover redux $(addsuffix .o, $(basename $(LIBS))) $(SRC)
.PHONY: verify

clean:
	rm -f *.o $(OUTPUT)
	rm -f lib/*.o
#	rm -f lib/stringBuffers.vfmanifest
.PHONY: clean

