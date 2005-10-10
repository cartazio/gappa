EXTRA_DIST = $(wildcard *.g)
CLEANFILES = $(wildcard failures-*.log)

check: check-indep check-coq

check-backend:
	for f in $(EXTRA_DIST); do \
	  ../src/gappa -B$(BACKEND) < "$$f" > /dev/null 2> /dev/null; \
	  return_code=$$?; \
	  if [ $${return_code} -ne 0 ]; then \
	    echo "$$f ($${return_code})"; \
	  fi; \
	done > "failures-$(BACKEND)-$$(date -Idate).log"

check-indep:
	$(MAKE) check-backend BACKEND=null

check-coq:
	$(MAKE) check-backend BACKEND=coq
