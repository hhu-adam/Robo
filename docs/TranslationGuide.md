
# Adding a new translation

Before you start working on a translation, please reach out to our Translation Coordinator [Konstantin Belyanin](https://github.com/k88-b) to make sure you are not duplicating ongoing efforts by other volunteers.

## 1. Translate the glossary

All translations files are contained in the folder `.i18n`. There's a subfolder for each language.  To add a translation to Pidgeonese, first create a new folder `.i18n/pg`, where `pg` is the ISO language code for Pidgeonese.  Then, copy the glossary from [.i18n/en/glossary.csv](https://github.com/hhu-adam/Robo/blob/main/.i18n/en/glossary.csv) to `.i18n/pg/glossary.csv` and translate the terms in this list.
The list is short, but you'll need to be familiar with the game and with its content in order to come up with good translations.

The first challenge is to find a good name for the Game itself and for the smart-elf that it features.  In German, the elf is called "Robo", in English "Scribble". What would work best in Pidgeonese?

Translating the planets and the characters that appear on them can also be tricky.  For example, the German version has a planet called "Robotswana".  That title obviously doesn't make sense in the English version.  In English, the planet is called "Ethiopia" (a weak reference to the many matrices `E i j` that appear on this planet).

Once you're done, delete all the comment lines (lines starting with `#`) from your csv file.

## 2. Pretranslate using machine translation

For this step, you will need access to a decent AI model.  If you don't have that, please ask our Translation Coordinator [Konstantin Belyanin](https://github.com/k88-b) to run this step for you.

### Option 2A:  Poedit + API key
The paid version of Poedit supports bulk machine translation using API keys from certain providers including OpenAI.  In detail, the machine translation process is as follows:

Build the project `Robo` with `lake build` to make sure the file `.i18n/de/Game.pot` is up-to-date.

In Poedit, go to `File` `>` `New From POT/PO File …` and open the file `.i18n/template/Game.pot`.  Select the language you want to translate into and save it as `.i18n/pg/Game.po`.

Then, select `Translation` `>` `Source Text` `>` `Load From Another File` and select one of the following two files:
```
  i18n/de/Game.po
  i18n/en/Game.po
```
We recommend using the German file (in the `de` folder) in this step, as the English version plays around with the English meaning of the names of certain Lean tactics, names which aren't actually visible in the strings.  For example, the English version might say:  "Now you can §0 the lemma", where §0 is a placeholder for the tactic `apply`.  There's no way a machine can figure out how to translate this.

Now import your glossary: Click `View` `>` `Show Terminology Tab`.  In the tab, click the little `+` symbol next to search box, and then `Import Glossary From CSV File…`.  Select the file `.i18n/pg/Glossary.csv` that you created above.

Next, select `Translation` `>` `Pretranslate`, tick `Use AI and machine translation`, and choose `GPT (OpenAI)` as translation tool.  Tick `Use glossary`.  Click on `Edit Custom Instructions …` and add the following prompt:

```
The strings are formatted in markdown, with §0, §1, §2, ... used as placeholders. Much of it is in dialogue form:

**Speaker A**: What speaker A says.

**Speaker B**:  What speaker B says.

Please retain as much of the original formatting as possible!  In particular, please preserve line breaks between paragraphs, and also any line breaks immediately before or after placeholders.  Ellipses should be denoted by the unicode symbol ….

The content of dialogues and other text is mathematical in nature.  The style should remain as fresh and informal as in the German original.
```
### Option 2B:  without Poedit

Decent models can also do all the above without Poedit.  Just ask it to create `.18n/pg/Game.po` in your desired language Pidgeonese (where `pg` in the file path is the ISO language code for Pidgeonese) based on the German version `.18n/de/Game.po`.  Include the following note on the file format in your instructions.

### Note on file format

In the entries in `.i18n/template/Game.pot`, lean snippets and latex snippets are replaced by
placeholders §0, §1, §2, … The contents of these snippets are present in the `.pot` and `.po` files as comments of the form `#. §n: ...`.

## 3. Review
You now need to go over the translations in Poedit line by line.  This is the hard part!  There are about 24.000 words in total, and you need to go over all of them.  Of course, the task can be distributed among several people, but then the difficulty lies in achieving consistency.

You can select any existing “original” language in this step, using the same method as in the previous step:

`Translation` `>` `Source Text` `>` `Load From Another File`.
