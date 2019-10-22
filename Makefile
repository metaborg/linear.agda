BUILD = build/sessions.agda

build/sessions.agda.tar.gz:
	rm -rf $(BUILD) && mkdir -p $(BUILD)
	cp -r README.md src/ lib/ $(BUILD)
	find $(BUILD) -iname *.agdai -exec rm {} \;
	tar cvzf $(BUILD).tar.gz --numeric-owner $(BUILD)
