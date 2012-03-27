#!/usr/bin/env python

# example notebook.py

import pygtk
pygtk.require('2.0')
import gobject 
import gtk

from types import *
from threading import *
from time import *
from datetime import *
from pytz import timezone
import pytz
import sys

from worldclockwindow import *
from evalframe import *
from gtksheet import *
from pg import *

gtk.gdk.threads_init()

def main():
    gtk.gdk.threads_enter()
    gtk.main()
    gtk.gdk.threads_leave()

if __name__ == "__main__":

    glock = Lock()

    notebook = gtk.Notebook()
    notebook.set_tab_pos(gtk.POS_TOP)
    
    window = WorldClockWindow(glock)
    window.start()
    window.add(notebook)

    #

    sheetf = gtk.Frame()
    sw = gtk.ScrolledWindow()
    sw.set_shadow_type(gtk.SHADOW_ETCHED_IN)
    sw.set_policy(gtk.POLICY_AUTOMATIC,
                  gtk.POLICY_AUTOMATIC)
    ss = Sheet()
    sw.add(ss)
    sheetf.add(sw)
    sheetf.show()
    notebook.append_page(sheetf, gtk.Label("sheet"))

    #

    evalf = EvalFrame(ss.ss)
    notebook.append_page(evalf, gtk.Label(evalf.get_label()))
    ss.ss.add_callback(evalf.update_vars_callback)

    #
    
    pgf1 = PGFrame("Calculus")
    notebook.append_page(pgf1, gtk.Label("Calculus"))

    #

    pgf2 = PGFrame("Lisp")
    notebook.append_page(pgf2, gtk.Label("Lisp"))

    #

    window.show_all()

    window.fullscreen()
    
    main()
    sys.exit(0)
