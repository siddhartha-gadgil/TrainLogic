#!/bin/bash
rm docs/_notebooks/notes/* || true
for note in notes/*.ipynb
do
    echo $note   
    jupyter nbconvert --to html --output $note.html $note
    MODDATE=$(stat -c %y build.sc)
    echo $MODDATE
    echo -e "---\ndate: $MODDATE\n---\n" > docs/_notebooks/$note.html
    cat notes/$note.html >> docs/_notebooks/$note.html
done