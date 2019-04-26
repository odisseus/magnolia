PROJECT = magnolia
DEPENDENCIES = lib/mercator.jar
MODULES = core

$(PROJECT).jar: compile
	jar -cf $(PROJECT).jar -C bin $(PROJECT)

lib/%.jar:
	mkdir -p lib
	cd $* && make
	for JAR in $(find $* -name '*.jar'); do cp $(JAR) lib/; done

compile: $(DEPENDENCIES)
	@scalac -version | grep 'version 2\.12\.' > /dev/null || echo "scalac is not version 2.12.x"
	mkdir -p bin
	$(foreach MODULE,$(MODULES),scalac -unchecked -feature -d bin -cp bin:lib/'*' src/$(MODULE)/*.scala)

.PHONY: compile
