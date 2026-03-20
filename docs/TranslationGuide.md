# Adding a new translation

## 1. Translate the glossary

All translations files are contained in the folder `.i18n`. There's a subfolder for each language.  To add a translation to Pidgeonese, first create a new folder `.i18n/pg`.  Then, copy the glossary from `.i18n/en/Glossary.csv` to `.i18n/pg/Glossary.csv` and translate the terms in this list.
The list is short, but you'll need to be familiar with the game and with its content in order to come up with good translations.

The first challenge is to find a good name for the Game itself and for the smart-elf that it features.  In German, the elf is called "Robo", in English "Scribble". What would work best in Pidgeonese?

Translating the planets and the characters that appear on them can also be tricky.  For example, the German version has a planet called "Robotswana".  That title obviously doesn't make sense in the English version.  In English, the planet is called "Ethiopia" (a weak reference to the many matrices `E i j` that appear on this planet).

Once you're done, delete all the comment lines (lines starting with `#`) from your csv file.  

## 2. Pretranslate using machine translation

For this step, you will need a paid version of Poedit, plus a (paid) OpenAI API key.  Or, you can simply contact [me](https://www.math.uni-duesseldorf.de/~zibrowius/), and I will do this step for you. 

In Poedit, go to `File` `>` `New From POT/PO File …` and open the file `.i18n/template/Game.pot`.  Select the language you want to translate into and save it as `.i18n/pg/Game.po`.

Then, select `Translation` `>` `Source Text` `>` `Load From Another File` and select one of the following two files:
```
  i18n/de/Game.po
  i18n/en/Game.po
```
We recommend using the German file (in the `de` folder) in this step, as the English version plays around with the English meaning of the names of certain Lean tactics, names which aren't actually visible in the strings.  For example, the English version might say:  "Now you can §0 the lemma", where §0 is a placeholder for the tactic `apply`.  There's no way a machine can figure out how to translate this.

Now import your glossary: Click `View` `>` `Show Terminology Tab`.  In the tab, click the litte `+` symbol next to search box, and then `Import Glossary From CSV File…`.  Select the file `.i18n/pg/Glossary.csv` that you created above.

Next, select `Translation` `>` `Pretranslate`, tick `Use AI and machine translation`, and choose `GPT (OpenAI)` as translation tool.  Tick `Use glossary`.  Click on `Edit Custom Instructions …` and add the following prompt:

```
The strings are formatted in markdown, with §0, §1, §2, ... used as placeholders. Much of it is in dialogue form:

**Speaker A**: What speaker A says.

**Speaker B**:  What speaker B says.

Please retain as much of the original formatting as possible!  In particular, please preserve line breaks between paragraphs, and also any line breaks immediately before or after placeholders.  Ellipses should be denoted by the unicode symbol ….  

The content of dialogues and other text is mathematical in nature.  The style should remain as fresh and informal as in the German original.
```


### Historical Note
We had previously experimented with Pretranslation using DeepL.  Unfortunately, DeepL has a tendency to get confused by formatting (line breaks, placeholders) in the input, and to destroy the formatting in the output. It even rendered some placeholders (§0, §1, …) as "Section 0", "Section 1" … . All of these issues aside, GPT appears to be better at translating idiomatic expressions. 

## 3. Review
You now need to go over the translations in Poedit line by line.  This is the hard part!  There are about 24.000 words in total, and you need to go over all of them.  Of course, the task can be distributed among several people, but then the difficulty lies in achieving consistency.

You can select any existing “original” language in this step, using the same method as in the previous step:   

`Translation` `>` `Source Text` `>` `Load From Another File`. 

