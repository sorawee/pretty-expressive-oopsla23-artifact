.PHONY: build doc-setup doc run-server

# Build and check the proofs
build:
	lake build

# Download packages for doc generation
doc-setup:
	lake -Kenv=dev update

# Generate HTML doc
doc:
	rm -rf build/doc
	lake -Kenv=dev build Pretty:docs

# Spawn a server for HTML viewing (not runnable inside Docker)
run-server:
	cd build/doc && python3 -m http.server
