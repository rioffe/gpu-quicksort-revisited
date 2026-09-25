# Makefile -- publishing targets for the gpu-quicksort-revisited repository.
#
#   make article     -> docs/index.html: docs/ARTICLE.md as ONE self-contained page (CSS
#                       inlined, mermaid diagrams rendered to embedded SVGs, math as MathML),
#                       the landing page GitHub Pages serves from docs/. Relative links are
#                       rewritten to point into the repository on GitHub; a floating table of
#                       contents sits left of the text on wide screens.
#   make clean       -> remove the generated page.
#
# Needs: pandoc, and for the diagrams, mermaid-filter with a Chrome/Chromium
# (without them the diagrams are left as code blocks).

ARTICLE_MD   := docs/ARTICLE.md
ARTICLE_HTML := docs/index.html
ARTICLE_CSS  := docs/article.css
FILTERS      := docs/title-from-h1.lua docs/repo-links.lua

# mermaid-filter: crisp, embeddable SVG; find a browser for puppeteer.
export MERMAID_FILTER_FORMAT ?= svg
CHROME := $(firstword $(wildcard /Applications/Google\ Chrome.app/Contents/MacOS/Google\ Chrome \
                                  /Applications/Chromium.app/Contents/MacOS/Chromium \
                                  /usr/bin/google-chrome /usr/bin/chromium /usr/bin/chromium-browser))
ifneq ($(CHROME),)
export PUPPETEER_EXECUTABLE_PATH ?= $(CHROME)
endif
MERMAID_FLAG := $(if $(shell command -v mermaid-filter 2>/dev/null),--filter mermaid-filter,)

.PHONY: article clean help

article: $(ARTICLE_HTML)

$(ARTICLE_HTML): $(ARTICLE_MD) $(ARTICLE_CSS) $(FILTERS) Makefile
	@echo "article: building $@ (self-contained; mermaid: $(if $(MERMAID_FLAG),svg inlined,filter not found -- diagrams left as code))"
	@printf '<style>\n' > $@.style.tmp; cat $(ARTICLE_CSS) >> $@.style.tmp; printf '</style>\n' >> $@.style.tmp
	pandoc $(ARTICLE_MD) --from=markdown-raw_tex --to=html5 --standalone --math-method=mathml \
	    --lua-filter=docs/title-from-h1.lua --lua-filter=docs/repo-links.lua \
	    --toc --toc-depth=2 --metadata "toc-title=Contents" \
	    --include-in-header=$@.style.tmp \
	    --embed-resources $(MERMAID_FLAG) --output $@
	@rm -f $@.style.tmp mermaid-filter.err
	@echo "Success! Created '$@'."

clean:
	rm -f $(ARTICLE_HTML) mermaid-filter.err

help:
	@echo "make targets: article, clean, help"
