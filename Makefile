all: index.html participation.html contact.html archive.html

index.html: index.org white_clean.theme
	emacs index.org --batch --eval \
		"(progn (setq org-html-validation-link nil) (org-html-export-to-html))"

participation.html: participation.org white_clean.theme
	emacs participation.org --batch --eval \
		"(progn (setq org-html-validation-link nil) (org-html-export-to-html))"

contact.html: contact.org white_clean.theme
	emacs contact.org --batch --eval \
		"(progn (setq org-html-validation-link nil) (org-html-export-to-html))"

archive.html: archive.org white_clean.theme
	emacs archive.org --batch --eval \
		"(progn (setq org-html-validation-link nil) (org-html-export-to-html))"

clean:
	rm -f index.html index.html~ participation.html participation.html~ \
		contact.html contact.html~ archive.html archive.html~

.PHONY: clean
