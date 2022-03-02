#!/bin/bash

if make quicker-install-bin-no-deps ;
then
    play ~/bin/NullpoMino7_5_0/res/se/combo1.wav
else
    play ~/bin/NullpoMino7_5_0/res/se/gem.wav
fi
