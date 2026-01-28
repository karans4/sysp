SYSP = sbcl --script sysp.lisp
CFLAGS = -std=c99 -pedantic -Wall -Wextra
RAYLIB_FLAGS = -I/usr/local/include -L/usr/local/lib -lraylib -lm -lGL -lpthread -ldl -lrt -lX11

TESTS = test-cons test-refcount test-qq test-macros test-macros2 test-infer \
        test-cons-edge test-refcount-stress test-memory-leaks test-portability

.PHONY: test test-all test-valgrind tictactoe clean clean-tests

# Run the test suite
test: test-all

test-all:
	./run-tests.sh

# Individual test compilation pattern rules
%.c: %.sysp sysp.lisp
	$(SYSP) $< $@

test-%: test-%.c
	gcc $(CFLAGS) $< -o $@

# Run tests with valgrind
test-valgrind: $(TESTS)
	@for t in $(TESTS); do \
		echo "=== Valgrind $$t ==="; \
		valgrind --leak-check=full --error-exitcode=1 ./$$t || true; \
	done

# Example targets
examples/hello: examples/hello.c
	gcc $(CFLAGS) -o $@ $<

examples/hello.c: examples/hello.sysp sysp.lisp
	$(SYSP) $< $@

tictactoe: examples/tictactoe
	@echo "Run with: ./examples/tictactoe"

examples/tictactoe: examples/tictactoe.c
	gcc -o $@ $< $(RAYLIB_FLAGS)

examples/tictactoe.c: examples/tictactoe.sysp sysp.lisp
	$(SYSP) $< $@

# Clean targets
clean: clean-tests
	rm -f examples/*.c examples/hello examples/tictactoe

clean-tests:
	rm -f test-*.c test-*.out test-*.valgrind
	rm -f $(TESTS)
