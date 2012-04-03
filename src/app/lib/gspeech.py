#!/usr/bin/python

import sys		#for cmd line argv
import time		#for delay
import pygst		#for playing mp3 stream
import gst		# " "


def speack(phrase):

    #tts_string = '+'.join(words)    
    tts_string = phrase.replace(" ", "+")

    music_stream_uri = 'http://translate.google.com/translate_tts?q=' + tts_string
    player = gst.element_factory_make("playbin", "player")
    player.set_property('uri', music_stream_uri)
    player.set_state(gst.STATE_PLAYING)
    

if __name__ == '__main__':
    speack("rock'n'roll doggy!!")
    time.sleep(12)
