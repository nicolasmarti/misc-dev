# Imports

from types import *

# for thread lock
from threading import *

# for time-related functions
from time import *
from datetime import *

# general
import sys
import os

# for ib
from ib.ext.Contract import Contract
from ib.ext.Order import Order
from ib.opt import ibConnection, message
from ib.ext.ScannerSubscription import ScannerSubscription
from ib.ext.ExecutionFilter import ExecutionFilter

import random

def watcher(msg):
    print "watcher: " + str(msg) + " :: " + str(type(msg))
    #print dir(msg)
    print "msg type name: " + str(msg.typeName)
    print "msg keys: " + str(msg.keys())
    print "msg items: " + str(msg.items())


con = ibConnection("127.0.0.1")

con.registerAll(watcher)

con.connect()

#print "con := " + str(dir(con))
#print "con.dispatcher := " + str(dir(con.dispatcher))
print "con.sender := " + str(dir(con.sender))
#print "con.receiver := " + str(dir(con.receiver))
#print con.dispatcher.messageTypes
#print "sender method name"
#for i in con.sender.clientMethodNames:
#    print "\t" + i

print "message.clientSocketMethods"
for i in message.clientSocketMethods:
    print "\t" + str(i)

#print "message.wrapperMethods"
#for i in message.wrapperMethods:
#    print "\t" + str(i)


sleep(3)

con.disconnect()
