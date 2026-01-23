SYSP = sbcl --script sysp.lisp
RAYLIB_FLAGS = -I/usr/local/include -L/usr/local/lib -lraylib -lm -lGL -lpthread -ldl -lrt -lX11

.PHONY: test tictactoe clean

test: examples/hello
	./examples/hello

tictactoe: examples/tictactoe
	@echo "Run with: ./examples/tictactoe"

examples/hello: examples/hello.c
	gcc -o $@ $<

examples/hello.c: examples/hello.sysp sysp.lisp
	$(SYSP) $< $@

examples/tictactoe: examples/tictactoe.c
	gcc -o $@ $< $(RAYLIB_FLAGS)

examples/tictactoe.c: examples/tictactoe.sysp sysp.lisp
	$(SYSP) $< $@

clean:
	rm -f examples/*.c examples/hello examples/tictactoe
