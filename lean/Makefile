.PHONY: doc run-server
doc:
	rm -rf build/doc
	lake -Kenv=dev build Pretty:docs

run-server:
	cd build/doc && python3 -m http.server
