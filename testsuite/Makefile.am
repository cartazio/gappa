EXTRA_DIST = $(wildcard *.g)
CLEANFILES = $(wildcard failures-*.log)

check: check-indep check-coq check-holl

check-backend:
	@logfile="failures-$(BACKEND)-$$(date -Idate).log"; \
	logtmp="log-$(BACKEND).tmp"; \
	outputtmp="output-$(BACKEND).tmp"; \
	cat /dev/null > "$$logtmp"; \
	cat /dev/null > "$$logfile"; \
	for f in $(EXTRA_DIST); do \
	  execute=0; \
	  if grep -e '^# back-end:' "$$f" > /dev/null; then \
	    grep -e '^# back-end:.*'$(BACKEND) "$$f" > /dev/null; \
	    execute=$$?; \
	  fi; \
	  if [ $$execute -eq 0 ]; then \
	    ../src/gappa -B$(BACKEND) < "$$f" > /dev/null 2> "$$outputtmp"; \
	    return_code=$$?; \
	    if [ $${return_code} -ne 0 ]; then \
	      (echo "*** $$f exited with error code $${return_code}"; cat "$$outputtmp"; echo) >> "$$logfile"; \
	      echo "$$f exited with error code $${return_code}" >> "$$logtmp"; \
	    fi; \
	    rm "$$outputtmp"; \
	  fi; \
	done; \
	nb=$$(cat "$$logtmp" | wc -l); \
	if [ $$nb -gt 0 ]; then \
	  echo "*** Failures for $(BACKEND) backend:"; \
	  cat "$$logtmp"; \
	else \
	  rm "$$logfile"; \
	fi; \
	rm "$$logtmp"

check-indep:
	$(MAKE) check-backend BACKEND=null

check-coq:
	$(MAKE) check-backend BACKEND=coq

check-holl:
	$(MAKE) check-backend BACKEND=holl
