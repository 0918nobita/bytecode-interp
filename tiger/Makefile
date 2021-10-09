MLB := tiger.mlb
SRCS := ast.sml env.sml interp.sml main.sml

build/tiger: $(MLB) $(SRCS)
	mkdir -p build
	mlton -output build/tiger tiger.mlb

.PHONY: clean
clean:
	rm -rf build
