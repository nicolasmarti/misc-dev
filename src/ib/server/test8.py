import Pyro.core

from ib.ext.Contract import Contract
from ib.ext.Order import Order
from ib.opt import ibConnection, message
from ib.ext.ScannerSubscription import ScannerSubscription

from time import *
from datetime import *

o = Pyro.core.getProxyForURI("PYRONAME://serverInterface")

c = Contract()
c.m_symbol = "DELL"
c.m_secType = 'STK'
c.m_exchange = "SMART"
c.m_currency = "USD"

mnow = datetime.now()

delta = timedelta(hours=2)
delta2 = timedelta(days=1)

mstr = (mnow - delta2 + delta).strftime("%Y%m%d %H:%M:%S")

print mstr

dataid = o.reqHistData(c, mstr, "1 D", "5 mins", "MIDPOINT", 0, 1)

print dataid

sleep(10)

hist = o.getHistData(dataid)

for i in hist:
    print i

o.cancelHistData(dataid)
