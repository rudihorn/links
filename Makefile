.PHONY: nc native clean tests install uninstall clean
.DEFAULT_GOAL: nc

nc:
	jbuilder build @install
	cp _build/default/bin/links.exe links
	ln -f -s links linx

native: nc

install:
	jbuilder install

uninstall:
	jbuilder uninstall

clean:
	jbuilder clean
	rm -rf *.install
	rm -rf links linx
