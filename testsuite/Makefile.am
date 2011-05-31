EXTRA_DIST = $(wildcard *.g)
CLEANFILES = $(wildcard failures-*.log)

check: check-indep check-coq check-holl

check-backend:
	@logfile="failures-$(BACKEND)-$$(date '+%Y-%m-%d').log"; \
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
	    timeout 5 ../src/gappa -B$(BACKEND) < "$$f" > /dev/null 2> "$$outputtmp"; \
	    return_code=$$?; \
	    if [ $${return_code} -ne 0 ]; then \
	      (echo "*** $$f exited with error code $${return_code}"; cat "$$outputtmp"; echo) >> "$$logfile"; \
	      echo "$$f exited with error code $${return_code}" >> "$$logtmp"; \
	    fi; \
	    rm "$$outputtmp"; \
	  fi; \
	done; \
	return_code=0; \
	if [ -s $$logtmp ]; then \
	  echo "*** Failures for $(BACKEND) backend:"; \
	  cat "$$logtmp"; \
	  return_code=1; \
	else \
	  rm "$$logfile"; \
	fi; \
	rm "$$logtmp"; \
	exit $${return_code}

check-indep:
	$(MAKE) check-backend BACKEND=null

check-coq:
	$(MAKE) check-backend BACKEND=coq

check-holl:
	$(MAKE) check-backend BACKEND=holl
