import pygtk
pygtk.require('2.0')
import gobject 
import gtk

from threading import *
import keybinding

from sets import *

import storegraph

from types import *

# some error dialog
def error_dialog(parent, msg):
    dialog = gtk.MessageDialog(parent,
                               gtk.DIALOG_DESTROY_WITH_PARENT,
                               gtk.MESSAGE_ERROR,
                               gtk.BUTTONS_OK,
                               msg)
    dialog.run()
    dialog.destroy()


class StoreFrame(gtk.Frame, Thread, keybinding.KeyBinding):

    def __init__(self, store = None):
        gtk.Frame.__init__(self)
        self.set_label("Store")

        # build a table to put all my stuffs
        self.table = gtk.Table(13, 16, True)
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
        
        self.liststore = gtk.TreeStore(str, str, str, str)
        self.liststore.set_sort_column_id(0, gtk.SORT_ASCENDING)
        self.liststore.set_sort_func(0, self.mysort)

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

        # an entry for loading modules
        self.entry = gtk.Entry()
        self.entry.set_can_focus(True)
        self.table.attach(self.entry, 0, 16, 12, 13)
        self.entry.connect("activate", self.load_module, None)

        # key event
        for i in [self.treeview, self.entry]:
            i.connect("key_press_event", self.key_pressed, None)
            i.connect("key_release_event", self.key_released, None)

        self.treeview.set_enable_search(False)

        self.treeview.connect("row-activated", self.local_clicked, None)

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

        # C-h -> show keybindings
        self.keyactions.append(
            ([Set([65507, 104])],
             lambda s: error_dialog(self.get_toplevel(), self.keycomments(gtk.gdk.keyval_name)),
             "show keybindings"
             )
            )

        # C-c C-k -> show local store
        self.keyactions.append(
            ([Set([65507, 99]), Set([65507,104])],
             lambda s: self.store.show_graph(),
             "show the local store dependency graph"
             )
            )

        # C-d -> remove a var
        self.keyactions.append(
            ([Set([65507, 100])],
             lambda s: self.del_var(),
             "delete a variable"
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

            if isinstance(key, str):
                try:
                    formula = self.store.formulas[key]
                except:
                    formula = "no formula"

                try:
                    keytype = type(self.store.values[key])
                except:
                    keytype = "no type"

                try:
                    value = self.store.values[key]
                    if isinstance(value, ModuleType):                    
                        l = self.store.store_eval("dir(" + key + ")")
                        value = str(l)
                    else:
                        value = str(value)

                except Exception as e:
                    print e
                    value = "no value"


                if key not in self.key2iter.keys():
                    self.key2iter[key] = self.liststore.append(None)

                self.liststore.set(self.key2iter[key], 0, str(key))
                self.liststore.set(self.key2iter[key], 1, formula)
                self.liststore.set(self.key2iter[key], 2, keytype)
                self.liststore.set(self.key2iter[key], 3, value)
                
                return

            if isinstance(key, tuple):

                l = []
                k = key
                while isinstance(k, tuple):
                    l.insert(0, k[1])
                    k = k[0]


                keyname = str(k)
                miter = None

                if k not in self.key2iter.keys():
                    self.key2iter[k] = self.liststore.append(miter)
                    miter = self.key2iter[k]
                    self.liststore.set(self.key2iter[k], 0, keyname)
                else:
                    miter = self.key2iter[k]                    

                for i in l:

                    keyname = str(i)
                    k = (k, i)

                    if k not in self.key2iter.keys():
                        self.key2iter[k] = self.liststore.append(miter)
                        miter = self.key2iter[k]
                        self.liststore.set(self.key2iter[k], 0, keyname)
                    else:
                        miter = self.key2iter[k]                    

                try:
                    formula = self.store.formulas[k]
                except:
                    formula = "no formula"

                try:
                    keytype = type(self.store.values[k])
                except:
                    keytype = "no type"
                    
                try:
                    value = self.store.values[k]
                    if isinstance(value, ModuleType):                    
                        l = self.store.store_eval("dir(" + k + ")")
                        value = str(l)
                    else:
                        value = str(value)

                except Exception as e:
                    print e
                    value = "no value"

                self.liststore.set(self.key2iter[k], 0, keyname)
                self.liststore.set(self.key2iter[k], 1, formula)
                self.liststore.set(self.key2iter[k], 2, keytype)
                self.liststore.set(self.key2iter[k], 3, value)

                return

        if action == "delete":
            key = param

            if isinstance(key, tuple):
                l = []
                k = key
                while isinstance(k, tuple):
                    l.insert(0, k[1])
                    k = k[0]
                return

            if isinstance(key, str):
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

    def local_clicked(self, treeview, path, viewcolumn, data):

        #print str(type(path))
        
        piter = treeview.get_model().get_iter(path)
        for i in path:
            #print str(treeview.get_model().get_value(piter, 0))
            piter = treeview.get_model().iter_parent(piter)

        piter = treeview.get_model().get_iter(path)
        varname = str(treeview.get_model().get_value(piter, 0))
        try:
            val = self.store[varname]
            if isinstance(val, ModuleType):
                #print "is a module"
                reload(val)
                self.store.update(varname)              
                
            else:
                self.store.update(varname)
        except Exception as e:
            print e
            self.store.update(varname)

    def load_module(self, widget, param):
        self.store[self.entry.get_text()] = "=__import__(\"" + self.entry.get_text() + "\")"
        self.entry.set_text("")
        return

    def del_var(self):
        path = self.treeview.get_cursor()[0]
        if path <> None:
            piter = self.treeview.get_model().get_iter(path)
            varname = str(self.treeview.get_model().get_value(piter, 0))
            self.store.__delitem__(varname)

    def mysort(self, treemodel, iter1, iter2, data = None):
        val1 = (treemodel.get(iter1, 0))[0]
        val2 = (treemodel.get(iter2, 0))[0]

        try:
            i1 = int(val1)
        except Exception as e:
            i1 = None

        try:
            i2 = int(val2)
        except:
            i2 = None

        if i1 <> None and i2 <> None:
            return int.__cmp__(i1, i2)

        if i1 == None and i2 == None:
            if val1 < val2: 
                return -1
            elif val1 > val2:
                return 1
            else:
                return 0
        
        if i1 == None:
            return 1
        else:
            return -1

        return 0

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






