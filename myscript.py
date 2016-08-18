class MyFunctions():
    def __init__( self):
        self.listOfItems = dict()
        self.map_cells = {}
        self.nearby_forts = {}

    def displayList( self):
        """Prints all items in listOfItems)"""
        print ("displayList")
        print (self.map_cells)
        for item in self.map_cells:
            print item

    def addToList(self):
        """Updates all mlb scores, and places results in a variable."""
        print ("addToList")
        self.map_cells = {'Name': 'Zara', 'Age': 7, 'Name2': 'Manni'};
        test = self.map_cells
        test.update({self.map_cells,12}) 
        #self.map_cells.update({'sdgfsfg': 'sdfgZara'}) 
        #self.map_cells.append("test")

f = MyFunctions()
f.displayList()
f.addToList()
f.displayList()