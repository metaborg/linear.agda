BUILDDIR = build
TARGET   = sessions.agda
BUILD    = $(BUILDDIR)/$(TARGET)

build/sessions.agda.tar.gz:
	rm -rf $(BUILD) && mkdir -p $(BUILD)
	cp -r README.md src/ lib/ $(BUILD)
	find $(BUILD) -iname *.agdai -exec rm {} \;
	cd $(BUILDDIR) && tar cvzf $(TARGET).tar.gz --numeric-owner $(TARGET)

examples:
	cd src && stack exec --package ieee754 --package text agda -- --compile Examples.agda
	./src/Examples
