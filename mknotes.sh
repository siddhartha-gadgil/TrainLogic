#!/bin/bash

for note in notes/*.ipynb
do
    echo $note   
    jupyter nbconvert --to html --output $note.html $note
    echo -e "---\n---\n" > docs/_notebooks/$note.html
    cat notes/$note.html >> docs/_notebooks/$note.html
done