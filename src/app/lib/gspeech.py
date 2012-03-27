#!/usr/bin/python

import sys		#for cmd line argv
import time		#for delay
import pygst		#for playing mp3 stream
import gst		# " "


def speack(words):

    tts_string = '+'.join(words)    

    music_stream_uri = 'http://translate.google.com/translate_tts?q=' + tts_string
    player = gst.element_factory_make("playbin", "player")
    player.set_property('uri', music_stream_uri)
    player.set_state(gst.STATE_PLAYING)
    


#speack(["the", "strategy", "is", "losing", "money", ",", "you", "dumb", "ass", "!"])
speack(["rock", "and", "roll", "doggy", "!"])


time.sleep(12)
