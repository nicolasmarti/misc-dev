import pygtk
pygtk.require('2.0')
import gobject 
import gtk

from threading import *
import keybinding

from sets import *

import gtksourceview2
import pango

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
        self.lm = gtksourceview2.LanguageManager()
        self.textbuffer = gtksourceview2.Buffer()
        self.textbuffer.set_data('languages-manager', self.lm)
        self.textview = gtksourceview2.View(self.textbuffer)

        self.textbuffer.set_highlight_matching_brackets(True)

        language = self.lm.guess_language("p.py")
        if language:
            self.textbuffer.set_language(language)
            self.textbuffer.set_highlight_syntax(True)

        self.sw = gtk.ScrolledWindow()
        self.sw.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)
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
            self.m_locals.add_callback(self.callback)
        except:
            pass                

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
        self.table.attach(self.sw, 10, 16, 0, 12)
        self.sw.show()
        self.treeview.show()

        self.treeview.set_enable_search(False)
        #self.liststore.set_enable_search(False)

        # dict of name to iterator
        self.key2iter = dict()

        self.treeview.connect("row-activated", self.local_clicked, None)

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

        # C-x C-f -> open a file
        self.keyactions.append(
            ([Set([65507, 120]), Set([65507,102])],
             lambda s: s.openfile()
             )
            )

        # C-x C-s -> save a file
        self.keyactions.append(
            ([Set([65507, 120]), Set([65507,115])],
             lambda s: s.savefile()
             )
            )

        # C-d -> remove a var
        self.keyactions.append(
            ([Set([65507, 100])],
             lambda s: self.del_var(),
             "delete a variable"
             )
            )

        # this is a historic of the commands and names
        self.hist = []
        # this is an historic of the formula
        self.histf = []
        # and a pointer
        self.histn = None
        # and a buffer for the current command
        self.savedcmd = None
        self.savedvar = None

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

        # add the new print function
        #self.m_locals["mprint"] = self.myprint

    # a special print for here
    def myprint(self, s):
        self.textbuffer2.set_text(str(s) + "\n")

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

    def callback(self, action, param):
        #print "evalframe.callback(" + str(action) + ", " + str(param) + ")"

        if action == "update" and param[0] in self.vars:
            key = param[0]
            
            try:
                formula = self.m_locals.formulas[key]
            except:
                formula = "no formula"

            try:
                keytype = type(self.m_locals.values[key])
            except:
                keytype = "no type"

            try:
                value = str(self.m_locals.values[key])
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
                self.vars.remove(key)


        return

    def myexec(self, data=None):

        self.hist.append((self.entry.get_text(), self.textbuffer.get_text(self.textbuffer.get_start_iter(), self.textbuffer.get_end_iter())))
        self.histn = None

        if self.entry.get_text() <> "":
            m_str = self.entry.get_text() + " = \"=" + self.textbuffer.get_text(self.textbuffer.get_start_iter(), self.textbuffer.get_end_iter()).replace("\n", "\\\n").replace("\"","\\\"") + "\""
            self.vars.append(self.entry.get_text())

        else:
            m_str = self.textbuffer.get_text(self.textbuffer.get_start_iter(), self.textbuffer.get_end_iter())

        self.histf.append(m_str)

        try:
            #exec m_str in globals(), self.m_locals
            self.m_locals.store_exec(m_str)
            #self.textbuffer2.set_text("")        
            self.m_start = self.textbuffer.get_end_iter()
            self.textbuffer.set_text("")
            self.entry.set_text("")
        except BaseException as e:
            if self.entry.get_text() <> "":
                self.vars.remove(self.entry.get_text())
            self.textbuffer2.set_text(str(e))        
            raise e


        self.textview.grab_focus()

    def myeval(self, data=None):
        self.hist.append(("", self.textbuffer.get_text(self.textbuffer.get_start_iter(), self.textbuffer.get_end_iter())))
        self.histn = None

        m_str = self.textbuffer.get_text(self.textbuffer.get_start_iter(), self.textbuffer.get_end_iter()).replace("\n", "\\\n")
        try:
            res = self.m_locals.store_eval(m_str)
            self.textbuffer2.set_text(str(res))        
            self.m_start = self.textbuffer.get_end_iter()
            self.textbuffer.set_text("")

        except BaseException as e:
            self.textbuffer2.set_text(str(e))        

            self.textview.grab_focus()



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
            self.savedvar = self.entry.get_text()

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
            self.histn = None
            return


        # change the current value of the buffer with the historical command
        self.textbuffer.set_text(self.hist[self.histn][1])
        self.entry.set_text(self.hist[self.histn][0])
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
            self.entry.set_text(self.savedvar)
        else:
            self.textbuffer.set_text(self.hist[self.histn][1])
            self.entry.set_text(self.hist[self.histn][1])
        
        return

    # open file
    def openfile(self):
        self.filew = gtk.FileSelection("File selection")
    
        def close(w):
            self.filew.hide()

        def fileok(w):
            self.filew.hide()   
            path = self.filew.get_filename()
            try:
                txt = open(path).read()
            except:
                return False

            self.textbuffer.set_text(txt)

            return True           
            
        self.filew.connect("destroy", close)
        self.filew.ok_button.connect("clicked", fileok)

        self.filew.show()

    def savefile(self):
        self.filew = gtk.FileSelection("File selection")
    
        def close(w):
            self.filew.hide()

        def fileok(w):            
            self.filew.hide()   

            f = open(self.filew.get_filename(), 'wb')

            for i in self.histf:
                f.write(i + "\n")               

            return True           
            
        self.filew.connect("destroy", close)
        self.filew.ok_button.connect("clicked", fileok)

        self.filew.show()

    def del_var(self):
        print self.treeview.get_cursor()[0]
        path = self.treeview.get_cursor()[0]
        if path <> None:
            piter = self.treeview.get_model().get_iter(path)
            varname = str(self.treeview.get_model().get_value(piter, 0))
            self.store.__delitem__(varname)


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
