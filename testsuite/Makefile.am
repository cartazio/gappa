EXTRA_DIST = $(wildcard *.g)
CLEANFILES = $(wildcard failures-*.log)

check: check-indep check-coq

check-backend:
	logfile="failures-$(BACKEND)-$$(date -Idate).log"; \
	for f in $(EXTRA_DIST); do \
	  ../src/gappa -B$(BACKEND) < "$$f" > /dev/null 2> /dev/null; \
	  return_code=$$?; \
	  if [ $${return_code} -ne 0 ]; then \
	    echo "$$f exited with error code $${return_code}"; \
	  fi; \
	done > "$$logfile"; \
	nb=$$(cat "$$logfile" | wc -l); \
	if [ $$nb -gt 0 ]; then \
	  echo "*** Failures for $(BACKEND) backend:"; \
	  cat "$$logfile"; \
	else \
	  rm "$$logfile"; \
	fi

check-indep:
	$(MAKE) check-backend BACKEND=null

check-coq:
	$(MAKE) check-backend BACKEND=coq
