BUILD_DIR := .build
DEFINITION := $(BUILD_DIR)/hcs-kompiled
SPECS ?= $(wildcard *-spec.k)
KOMPILE ?= kompile
KPROVE ?= kprove
KPROVE_FLAGS ?=

# K 7.1.337 on Ubuntu 24.04, pinned to the tested image digest.
K_IMAGE := runtimeverificationinc/kframework-k:ubuntu-noble-7.1.337@sha256:eaa1908aca723f5cb6de965e9b1ce1b4b4ae5e1f7aeb5451ec92a7aff5ad9d19
DOCKER_RUN = docker run --rm --network none --user "$$(id -u):$$(id -g)" \
	--mount "type=bind,source=$(CURDIR),target=/work" --workdir /work $(K_IMAGE)

.PHONY: all build verify clean docker-build docker-verify

all: verify

build: $(DEFINITION)/timestamp

$(DEFINITION)/timestamp: hcs.k Makefile
	$(KOMPILE) hcs.k --backend haskell --output-definition $(DEFINITION)

verify: build
	@set -eu; for spec in $(SPECS); do \
		labels=$$(sed -n 's/^[[:space:]]*\[label(\([^)]*\))\][[:space:]]*$$/\1/p' "$$spec"); \
		if [ -n "$$labels" ]; then \
			claims=$$(grep -c '^[[:space:]]*claim ' "$$spec"); \
			if [ "$$claims" -ne "$$(printf '%s\n' "$$labels" | wc -l)" ]; then \
				printf 'Every claim in %s must have its own [label(...)] line\n' "$$spec" >&2; \
				exit 1; \
			fi; \
			for label in $$labels; do \
				printf 'Proving %s: %s\n' "$$spec" "$$label"; \
				$(KPROVE) "$$spec" --definition $(DEFINITION) --claims "$$label" $(KPROVE_FLAGS); \
			done; \
		else \
			printf 'Proving %s\n' "$$spec"; \
			$(KPROVE) "$$spec" --definition $(DEFINITION) $(KPROVE_FLAGS); \
		fi; \
	done

docker-build:
	$(DOCKER_RUN) make build

docker-verify:
	$(DOCKER_RUN) make verify SPECS="$(SPECS)" KPROVE_FLAGS="$(KPROVE_FLAGS)"

clean:
	rm -rf $(BUILD_DIR)
