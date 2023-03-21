.PHONY: build doc run-server

# Build everything
build:
	dune build

# Generate HTML doc
doc:
	dune build @doc

# Spawn a server for HTML viewing (not runnable inside Docker)
run-server:
	cd _build/default/_doc/_html/ && python3 -m http.server
