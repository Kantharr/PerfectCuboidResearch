.PHONY: all check verify verify-crosscheck verify-big clean

all: perfect_cuboid.pdf

perfect_cuboid.pdf: perfect_cuboid.tex
	./build.sh

check:
	python3 check.py perfect_cuboid.tex

verify:
	python3 verify.py 2000

verify-crosscheck:
	gcc -O2 -o verify verify.c -lm
	python3 crosscheck.py 2000

verify-big: verify-crosscheck
	./verify 7000

clean:
	latexmk -C perfect_cuboid.tex >/dev/null 2>&1 || true
	rm -f build.log verify verify.exe
