"""
a first temptative to build a graphical sheet in gtk using TreeView
"""

import pygtk
pygtk.require('2.0')
import gtk
from gtk import gdk
import re
from string import join, ascii_uppercase

from storegraph import *


from types import *


class CellRender(gtk.CellRendererText):

    def __init__(self, col, store, ss):

        gtk.CellRendererText.__init__(self)

        self.connect('editing-started', self.editing_start)
        self.connect('editing-canceled', self.editing_cancel)

        self.store = store
        self.ss = ss

        self.ss._debug = False

        self.col = col

    def editing_start(self, cell, editable, path, user_param = None):
        #print "editing_start"
        try:
            f = self.ss.getformula(colnum2colname(self.col - 1) + str(int(path) + 1))
            editable.set_text(f[1:])
        except:
            pass

    def editing_cancel(self, cell, user_param = None):
        #print "editing_cancel"
        pass

# some entry used for external needs
class MyEntry(gtk.Entry):

    def key_pressed(self, widget, event, data=None):        
        #print "MyEntry " + str(event.keyval)
        if (event.keyval == 65293):
            text = self.get_text()
            #print "MyEntry enter pressed! " + text
            self.set_text("")
            self.disconnect(self.keypressedid)
            self.set_editable(False)
            self.set_can_focus(False)
            action = self.on_enter
            action(text)


    def __init__(self):

        gtk.Entry.__init__(self)

        self.on_enter = None

        self.set_editable(False)

        #self.modify_base(gtk.STATE_NORMAL, gtk.gdk.color_parse('black'))
        
        self.set_can_focus(False)

    def setquestion(self, text, action):
        self.on_enter = action
        self.set_editable(True)
        self.set_text(text)
        self.keypressedid = self.connect("key_press_event", self.key_pressed, None)
        self.set_can_focus(True)
        self.grab_focus()


class Sheet(gtk.TreeView):

    def __init__(self, numCols = 100, numRows = 100, ss = None):

        gtk.TreeView.__init__(self)

        if ss == None:
            self.ss = Storegraph(_globals = globals())
        else:
            self.ss = ss
        
        # the underlying ss        
        self.ss.add_callback(self.setcell)

        # numbers of row / columns
        self.numCols = numCols
        self.numRows = numRows

        # build the storage of data
        types =  [str]*(self.numCols+1)
        self.store = gtk.ListStore(*types)

        # fill it with empty stuffs
        for i in range(self.numRows):
            self.store.append([str(i+1)] + [""] * self.numCols)

        # add columns
        for i in range(self.numCols + 1):
            cellrenderertext = CellRender(i, self.store, self.ss)

            cellrenderertext.connect('edited', self.edited_cb, i)

            if i > 0:
                cellrenderertext.set_property('editable', True)

            column = gtk.TreeViewColumn('%s'% colnum2colname(i - 1) if (i > 0) else "", cellrenderertext, text=i)

            if False:
                column.set_sizing(gtk.TREE_VIEW_COLUMN_AUTOSIZE)
                column.set_min_width(100)
            else:
                column.set_fixed_width(100)
                column.set_sizing(gtk.TREE_VIEW_COLUMN_FIXED)

            if i == 0:
                self.firstcolumn = column

            self.append_column(column)

        

        self.set_rules_hint(True)

        self.set_model(self.store)

        self.connect("key_press_event", self.key_pressed, None)
        self.connect("key_release_event", self.key_released, None)
        self.connect("row-activated", self.raw_activated, None)

        self.set_enable_search(False)

        #self.set_property('enable-grid-lines', True)
        
        self.set_grid_lines(gtk.TREE_VIEW_GRID_LINES_BOTH)

        self.get_settings().set_property("gtk-error-bell", False)

    def raw_activated(self, treeview, path, view_column, user_param1 = None):
        #print "raw_activated"
        pass

    def key_pressed(self, widget, event, data=None):        
        #global win
        # "=" ==> edit the cell        
        cursor = self.get_cursor()
        row = cursor[0][0]
        renders = cursor[1].get_cell_renderers()
        col = renders[0].col


        title = str((row, col))
        self.firstcolumn.set_title(title)
        
        # '='
        if event.keyval == 61:
            print (row, col)

        # Delete
        if event.keyval == 65535:
            key = colnum2colname(col - 1) + str(row + 1)
            self.ss.remove_key(key)
            print self.ss

        # Esc 
        if event.keyval == 65307:
            gtk.main_quit()

    def key_released(self, widget, event, data=None):      
        try:
            global win

            cursor = self.get_cursor()
            row = cursor[0][0]
            renders = cursor[1].get_cell_renderers()
            col = renders[0].col

            title = str((row, col))
            self.firstcolumn.set_title(title)
        
            key = colnum2colname(col - 1) + str(row + 1)
            f = self.ss.getformula(key)            
            win.set_title((str(f) if f <> None else key) + " := " + str(self.ss[key]) + repr(type(self.ss[key])))

        except:
            return 

    def edited_cb(self, cell, path, new_text, user_data = None):
        try:
            self.ss[colnum2colname(user_data - 1) + str(int(path) + 1)] = "=" + new_text
        except Exception as e:
            self.ss[colnum2colname(user_data - 1) + str(int(path) + 1)] = str(e)
        
    def setcell(self, action, param):
        #print "setcell " + str(action) + " " + str(param)
        try:
            if action == "update":
                key = param[0]
                value = param[1]

                (row, col) = key2cell(key)

                self.store[row][col] = str(value)

                return

            if action == "delete":
                key = param

                (row, col) = key2cell(key)

                self.store[row][col] = ""
                return
        except Exception as e:
            #print str(e)
            pass
            

if __name__ == '__main__':
    
    sw = gtk.ScrolledWindow()
    sw.set_shadow_type(gtk.SHADOW_ETCHED_IN)
    sw.set_policy(gtk.POLICY_AUTOMATIC,
                  gtk.POLICY_AUTOMATIC)

    sheet = Sheet()
    sw.add(sheet)
    win = gtk.Window()
    win.add(sw)

    win.connect('destroy', lambda win: gtk.main_quit())

    win.resize(800, 600)

    win.show_all()

    win.maximize()

    gtk.main()
