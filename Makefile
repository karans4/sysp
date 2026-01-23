.PHONY: test clean

test: examples/hello
	./examples/hello

examples/hello: examples/hello.c
	gcc -o $@ $<

examples/hello.c: examples/hello.sysp sysp.lisp
	sbcl --script sysp.lisp $< $@

clean:
	rm -f examples/*.c examples/hello
