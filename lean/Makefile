.PHONY: doc run-server
doc:
	rm -r build/doc
	lake -Kenv=dev build Pretty:docs

run-server:
	cd build/doc && python3 -m http.server
