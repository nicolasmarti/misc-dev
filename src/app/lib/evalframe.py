import pygtk
pygtk.require('2.0')
import gobject 
import gtk

from threading import *
import keybinding

from sets import *

import storegraph

class EvalFrame(gtk.Frame, Thread, keybinding.KeyBinding):
    
    def __init__(self, _locals = None):
        gtk.Frame.__init__(self)
        self.set_label("Evaluator")
        
        # build a table to put all my stuffs
        self.table = gtk.Table(12, 16, True)
        self.table.show()
        self.add(self.table)

        #add an entry 
        self.entry = gtk.Entry()
        self.entry.set_can_focus(True)
        self.table.attach(self.entry, 0, 10, 0, 1)

        # build scrolled window and textview
        self.sw = gtk.ScrolledWindow()
        self.sw.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)
        self.textview = gtk.TextView()
        self.textbuffer = self.textview.get_buffer()
        self.sw.add(self.textview)
        self.sw.show()
        self.textview.show()
        self.table.attach(self.sw, 0, 10, 1, 8)

        # build the result textview
        self.sw2 = gtk.ScrolledWindow()
        self.sw2.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)
        self.textview2 = gtk.TextView()
        self.textview2.set_editable(False)
        self.textbuffer2 = self.textview2.get_buffer()
        self.textview2.show()
        self.sw2.add(self.textview2)
        self.sw2.show()
        self.table.attach(self.sw2, 0, 10, 8, 12)

        # the button
        #self.button = gtk.Button(label="execute(C-c C-c)")
        #self.button.show()
        #self.table.attach(self.button, 3, 6, 8, 9)
        #self.button.connect("clicked", self.myexec, None)

        #self.button = gtk.Button(label="eval(C-c C-n)")
        #self.button.show()
        #self.table.attach(self.button, 0, 3, 8, 9)
        #self.button.connect("clicked", self.myeval, None)

        #self.button = gtk.Button(label="???")
        #self.button.show()
        #self.table.attach(self.button, 6, 10, 8, 9)

        if _locals == None:
            self.m_locals = locals()
        else:
            self.m_locals = _locals

        try:
            self.m_locals.add_callback(self.update_vars_callback)
        except:
            pass                


        # tree view
        self.sw3 = gtk.ScrolledWindow()
        self.sw3.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)
        self.treestore = gtk.TreeStore(str)
        self.treeview = gtk.TreeView(self.treestore)
        self.tvcolumn = gtk.TreeViewColumn('local name')
        self.treeview.append_column(self.tvcolumn)
        self.treeview.connect("row-activated", self.local_clicked, None)
        self.cell = gtk.CellRendererText()
        self.tvcolumn.pack_start(self.cell, True)
        self.tvcolumn.add_attribute(self.cell, 'text', 0)
        self.sw3.add(self.treeview)
        self.table.attach(self.sw3, 10,16, 0, 12)
        self.sw3.show()
        self.treeview.show()

        self.name2iter = dict()

        self.vars = []

        for i in [self.textview, self.entry]:
            i.connect("key_press_event", self.key_pressed, None)
            i.connect("key_release_event", self.key_released, None)

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

        # C-c C-k -> show local store
        self.keyactions.append(
            ([Set([65507, 99]), Set([65507,104])],
             lambda s: self.m_locals.show_graph(),
             "show the local store dependency graph"
             )
            )

        # C-c C-c -> execute
        self.keyactions.append(
            ([Set([65507, 99]), Set([65507,99])],
             lambda s: self.myexec(),
             "execute"
             )
            )

        # C-c C-n -> eval
        self.keyactions.append(
            ([Set([65507, 99]), Set([65507,110])],
             lambda s: self.myeval(),
             "evaluate"
             )
            )

        # C-c C-d -> focus the entry
        self.keyactions.append(
            ([Set([65507, 99]), Set([65507,100])],
             lambda s: self.entry.grab_focus(),
             "focus the entry"
             )
            )

        # C-k -> clear buffer and entry
        self.keyactions.append(
            ([Set([65507, 107])],
             lambda s: self.clear_buffers(),
             "clear buffer and entry"
             )
            )

        # C-h -> show keybindings
        self.keyactions.append(
            ([Set([65507, 104])],
             lambda s: self.textbuffer2.set_text(self.keycomments(gtk.gdk.keyval_name)),
             "show keybindings"
             )
            )

        # this is a historic of the commands
        self.hist = []
        # and a pointer
        self.histn = None
        # and a buffer for the current command
        self.savedcmd = None

        # C-up -> get the previous command
        self.keyactions.append(
            ([Set([65507, 65362])],
             lambda s: self.hist_previous(),
             "get previous command"
             )
            )

        # C-down -> get the next command
        self.keyactions.append(
            ([Set([65507, 65364])],
             lambda s: self.hist_next(),
             "get next command"
             )
            )

        self.get_settings().set_property("gtk-error-bell", False)

    def clear_buffers(self):
        self.textbuffer2.set_text("")  
        self.entry.set_text("")  
        self.textbuffer.set_text("")  
        return

    # key callback
    def key_pressed(self, widget, event, data=None):        
        
        self.keypressed(event.keyval)
        if event.state & gtk.gdk.CONTROL_MASK: self.keypressed(self.ctrl)
        #print str(event.keyval) + " from " + str(widget)
        #self.textview.grab_focus()
        return

    def key_released(self, widget, event, data=None):        
        self.keyreleased(event.keyval)
        if not (event.state & gtk.gdk.CONTROL_MASK): self.keyreleased(self.ctrl)
        #self.textview.grab_focus()
        return

    def update_vars_callback(self, action, param):
        try:
            #print "update!"
            if action == "update":
                #print "param[0] :=" + str(param[0])
                key = param[0]
                if key in self.name2iter.keys():
                    name = str(key)
                    try:
                        name = name + " := " + self.m_locals.getformula(key)[1:]
                    except:
                        pass
                    try:
                        name = name + " == " + str(self.m_locals.getvalue(key))
                    except:
                        pass
                    self.treestore.set(self.name2iter[key], 0, name)

            #print "update!"
            if action == "delete":
                #print "param[0] :=" + str(param[0])
                key = param
                if key in self.name2iter.keys():
                    self.treestore.remove(self.name2iter[key])
                    del(self.name2iter[key])
                    self.vars.remove(key)

        except Exception as e:
            print "error := " + str(e)
            pass

        self.update_vars()

    def update_vars(self):
        #print "update_vars"
        # is there new vars ?
        for d in self.vars:
            if not d in self.name2iter.keys():
                # a new local var
                name = str(d)
                try:
                    name = name + " := " + self.m_locals.getformula(d)[1:]
                except:
                    pass
                try:
                    name = name + " == " + str(self.m_locals.getvalue(d))
                except:
                    pass
                iter = self.treestore.append(None, [name])
                self.name2iter[d] = iter
            # have to do those in ...
        
        return

    def myexec(self, data=None):
        if self.entry.get_text() <> "":
            m_str = self.entry.get_text() + " = \"=" + self.textbuffer.get_text(self.textbuffer.get_start_iter(), self.textbuffer.get_end_iter()).replace("\n", "\\\n").replace("\"","\\\"") + "\""

        else:
            m_str = self.textbuffer.get_text(self.textbuffer.get_start_iter(), self.textbuffer.get_end_iter())
        try:
            #exec m_str in globals(), self.m_locals
            self.m_locals.store_exec(m_str)
            if self.entry.get_text() <> "":
                self.vars.append(self.entry.get_text())
            self.textbuffer2.set_text("")        
            self.m_start = self.textbuffer.get_end_iter()
            self.textbuffer.set_text("")
            self.entry.set_text("")
        except BaseException as e:
            self.textbuffer2.set_text(str(e))        
            raise e

        self.update_vars()
                
        self.hist.append(m_str)
        self.histn = None

        self.textview.grab_focus()

    def myeval(self, data=None):
        m_str = self.textbuffer.get_text(self.textbuffer.get_start_iter(), self.textbuffer.get_end_iter())
        try:
            res = self.m_locals.store_eval(m_str)
            self.textbuffer2.set_text(str(res))        
            self.m_start = self.textbuffer.get_end_iter()
            self.textbuffer.set_text("")

        except BaseException as e:
            self.textbuffer2.set_text(str(e))        

            self.textview.grab_focus()

        self.hist.append(m_str)
        self.histn = None

    def local_clicked(self, treeview, path, viewcolumn, data):
        #print "treeview: " + str(treeview) + " :: " + str(type(treeview))
        #print "path: " + str(path) + " :: " + str(type(path))
        #print "viewcolumn: " + str(viewcolumn) + " :: " + str(type(viewcolumn))
        #print "data: " + str(data) + " :: " + str(type(data))

        piter = treeview.get_model().get_iter(path)
        varname = str(treeview.get_model().get_value(piter, 0))
        self.textbuffer.insert(self.textbuffer.get_end_iter(), varname)
        self.textview.grab_focus()

    def hist_previous(self):

        # first time we look for the historic, or if the pointer is on the length of the hist, we need to save the current command
        if self.histn == None or self.histn == len(self.hist):
            self.savedcmd = self.textbuffer.get_text(self.textbuffer.get_start_iter(), self.textbuffer.get_end_iter())

        # first set up the pointer
        if self.histn == None:
            self.histn = len(self.hist) - 1
        else:
            self.histn -= 1

        # make sure we are at least at 0
        if self.histn < 0:
            self.histn = 0

        # and make sure it points to something
        if self.histn >= len(self.hist):
            self.hist = None
            return


        # change the current value of the buffer with the historical command
        self.textbuffer.set_text(self.hist[self.histn])
        return
        
    def hist_next(self):
        # if the pointer is not set, do nothing
        if self.histn == None: return

        # else update it
        self.histn += 1

        # if it is gt to the length of the historic, then we assign to the length, and show the current command
        if self.histn >= len(self.hist): 
            self.histn = len(self.hist)
            self.textbuffer.set_text(self.savedcmd)
        else:
            self.textbuffer.set_text(self.hist[self.histn])
        
        return

if __name__ == '__main__':
    
    ss = storegraph.Storegraph(_globals = globals())

    evalf = EvalFrame(ss)

    win = gtk.Window()
    win.add(evalf)

    win.connect('destroy', lambda win: gtk.main_quit())

    win.resize(800, 600)

    win.show_all()

    win.maximize()

    gtk.main()
