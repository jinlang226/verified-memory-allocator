.PHONY: all verify build libc bench clean

VERUS ?= verus

all: build

# Build the libc rlib that verus-mimalloc links against.
build/liblibc.rlib:
	./setup-libc-dependency.sh

libc: build/liblibc.rlib

verify: build/liblibc.rlib
	cd verus-mimalloc && VERUS_PATH=$(VERUS) ./verify.sh

build: build/liblibc.rlib
	./build.sh

bench:
	./build-benchmarks-and-allocators.sh

clean:
	rm -rf build
	cd test_libc && cargo clean --release
