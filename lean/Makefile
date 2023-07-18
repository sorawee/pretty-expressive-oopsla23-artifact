.PHONY: build doc-setup doc run-server

# Build and check the proofs
build:
	racket scripts/gen-main.rkt
	lake build

# Download packages for doc generation
doc-setup:
	lake -Kenv=dev update

# Generate HTML doc; remove build/doc to prevent content mangling
doc:
	racket scripts/gen-main.rkt
	rm -rf build/doc
	lake -Kenv=dev build Pretty:docs

# Spawn a server for HTML viewing (not runnable inside Docker)
run-server:
	cd build/doc && python3 -m http.server

graph:
	racket scripts/gen-main.rkt
	lake exe graph --to Pretty --reduce
	racket scripts/process-graph.rkt
	dot -Tpng import_graph.dot -o import_graph.png
