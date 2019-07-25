# Dynamix

## Project setup
Before importing the Dynamix projects, make sure you have a working [FrameVM](https://www.github.com/metaborgcube/framevm) installation.
After this you can import the relevant Dynamix projects using `File -> Import -> Maven -> Existing Maven projects`.
- `dynamix`: The main project containing the syntax and interpretation rules
- `dynamix.example`: Example syntax sketches. Note that these cannot be interpreted as there is no host language present.
- `dynamix.test`: Project containing tests. This project is currently empty

## Using Dynamix in a host language
In order to create a Dynamix specification for your language you have to host Dynamix in your project.
This is done by adding a dependency on Dynamix and importing the relevant Dynamix source files.
Note that in order to import Dynamix, you also have to import the FrameVM.

Importing Dynamix can be done by adding the following imports to your projects `metaborg.yaml`-file:
```yaml
dependencies:
  compile:
  - org.metaborg:lang.dynamix:0.1.0-SNAPSHOT
  source:
  - org.metaborg:lang.dynamix:0.1.0-SNAPSHOT
  - org.metaborg.lang:framevm:1.1.0
```
And by adding the same dependencies to you languages `pom.xml`-file:
```xml
<dependencies>
 <dependency>
 	<groupId>org.metaborg</groupId>
 	<artifactId>lang.dynamix</artifactId>
 	<version>0.1.0-SNAPHOT</version>
 	<scope>runtime</scope>
	<type>spoofax-language</type>
 </dependency>
 <dependency>
 	<groupId>org.metaborg.lang</groupId>
 	<artifactId>framevm</artifactId>
 	<version>1.1.0</version>
 	<scope>runtime</scope>
	<type>spoofax-language</type>
 </dependency>
</dependencies>
```

After configuring your dependencies this way, you have to make the Dynamix menu-item appear for language files of your host language.
For this you have to take the following steps:
- Add `dynamix/compile` as an import to your projects `Main.esv`-file
- Add `dynamix/compile` as an import to your `trans/<LANGUAGE>.str`-file

After taking all the configuration steps, you are able to write a Dynamix specification for your language.
Make sure that the module name of your main Dynamix file is `dynamic-semantics` and that the following message is printed to the console:
```
| INFO  | Dynamix                        - Writing compiled Dynamix spec to 'src-gen/dynamix/<modulename>.dnxc'
```

Finally you can compile your languages source files to FrameVM bytecode by clicking `Spoofax -> Dynamix -> Compile to FVM`.
