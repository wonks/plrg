index.html: index.org white_clean.theme
	emacs index.org --batch --eval \
		"(progn (setq org-html-validation-link nil) (org-html-export-to-html))"

clean:
	rm -f index.html index.html~

.PHONY: clean
