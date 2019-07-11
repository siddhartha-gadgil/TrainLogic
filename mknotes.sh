#!/bin/bash

for note in notes/*.ipynb
do
    echo $note
    jupyter nbconvert --to html --output ../docs/_notebooks/$note.html $note
done