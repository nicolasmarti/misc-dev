import pygtk
pygtk.require('2.0')
import gobject 
import gtk

from threading import *
import keybinding

from sets import *

import storegraph

from types import *

class StoreFrame(gtk.Frame, Thread, keybinding.KeyBinding):

    def __init__(self, store = None):
        gtk.Frame.__init__(self)
        self.set_label("Store")

        # build a table to put all my stuffs
        self.table = gtk.Table(12, 16, True)
        self.table.show()
        self.add(self.table)

        # the store
        if store == None:
            self.store = Storegraph(_globals = globals())
        else:
            self.store = store

        self.store.add_callback(self.callback)

        # view
        self.sw = gtk.ScrolledWindow()
        self.sw.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)

        self.liststore = gtk.ListStore(str, str, str, str)
        self.treeview = gtk.TreeView(self.liststore)

        self.fields = ["key", "formula", "type", "value"]

        self.columns = range(0, len(self.fields))
        self.cells = range(0, len(self.fields))                            

        for i in range(0, len(self.fields)):
            self.columns[i] = gtk.TreeViewColumn(self.fields[i])
            self.treeview.append_column(self.columns[i])
            self.cells[i] = gtk.CellRendererText()
            self.columns[i].pack_start(self.cells[i], True)
            self.columns[i].add_attribute(self.cells[i], 'text', i)

        self.sw.add(self.treeview)
        self.table.attach(self.sw, 0, 16, 0, 12)
        self.sw.show()
        self.treeview.show()

        self.treeview.set_enable_search(False)
        #self.liststore.set_enable_search(False)

        # dict of name to iterator
        self.key2iter = dict()

        # key event
        for i in [self.treeview]:
            i.connect("key_press_event", self.key_pressed, None)
            i.connect("key_release_event", self.key_released, None)

        self.treeview.set_enable_search(False)

        self.treeview.set_grid_lines(gtk.TREE_VIEW_GRID_LINES_HORIZONTAL)

        # initialize super class keybing
        keybinding.KeyBinding.__init__(self)
        self.ctrl = 65507

        # C-x C-c -> close the application
        self.keyactions.append(
            ([Set([65507, 120]), Set([65507,99])],
             lambda s: gtk.main_quit(),
             "close the application"
             )
            )

        # C-x C-l -> open a file
        self.keyactions.append(
            ([Set([65507, 120]), Set([65507,108])],
             lambda s: self.load(),
             "load a store"
             )
            )
        
        # C-x C-s -> save a file
        self.keyactions.append(
            ([Set([65507, 120]), Set([65507,115])],
             lambda s: self.save(),
             "save a store"
             )
            )

    # key callback
    def key_pressed(self, widget, event, data=None):        
        
        self.keypressed(event.keyval)
        if event.state & gtk.gdk.CONTROL_MASK: self.keypressed(self.ctrl)
        #print str(event.keyval) + " from " + str(widget)
        return

    def key_released(self, widget, event, data=None):        
        self.keyreleased(event.keyval)
        if not (event.state & gtk.gdk.CONTROL_MASK): self.keyreleased(self.ctrl)
        return

    def callback(self, action, param):
        #print "storeframe.callback(" + str(action) + ", " + str(param) + ")"

        if action == "update":
            key = param[0]
            
            try:
                formula = self.store.formulas[key]
            except:
                formula = "no formula"

            try:
                keytype = type(self.store.values[key])
            except:
                keytype = "no type"

            try:
                value = str(self.store.values[key])
            except:
                value = "no value"


            if key not in self.key2iter.keys():
                self.key2iter[key] = self.liststore.append()

            self.liststore.set(self.key2iter[key], 0, str(key))
            self.liststore.set(self.key2iter[key], 1, formula)
            self.liststore.set(self.key2iter[key], 2, keytype)
            self.liststore.set(self.key2iter[key], 3, value)

        if action == "delete":
            key = param
            if key in self.key2iter.keys():
                self.liststore.remove(self.key2iter[key])
                del(self.key2iter[key])


        return

    def load(self):
        self.filew = gtk.FileSelection("File selection")
    
        def close(w):
            self.filew.hide()

        def fileok(w):
            self.filew.hide()   
            self.store.load(open(self.filew.get_filename(), 'rb'))
            return True           
            
        self.filew.connect("destroy", close)
        self.filew.ok_button.connect("clicked", fileok)

        self.filew.show()

    def save(self):
        self.filew = gtk.FileSelection("File selection")
    
        def close(w):
            self.filew.hide()

        def fileok(w):
            self.filew.hide()   
            self.store.save(open(self.filew.get_filename(), 'wb'))
            return True           
            
        self.filew.connect("destroy", close)
        self.filew.ok_button.connect("clicked", fileok)

        self.filew.show()


if __name__ == '__main__':
    
    sw = gtk.ScrolledWindow()
    sw.set_shadow_type(gtk.SHADOW_ETCHED_IN)
    sw.set_policy(gtk.POLICY_AUTOMATIC,
                  gtk.POLICY_AUTOMATIC)

    store = storegraph.Storegraph(_globals = globals())

    evalf = StoreFrame(store)
    sw.add(evalf)

    win = gtk.Window()
    win.add(sw)

    win.connect('destroy', lambda win: gtk.main_quit())

    win.resize(800, 600)

    win.show_all()

    win.maximize()

    gtk.main()





