CFLAGS=-Wall -DNDEBUG -O3
all: mcaiger
OBJ=mcaiger.o ../aiger/aiger.o ../picosat/picosat.o
mcaiger: $(OBJ)
	$(CC) $(CFLAGS) -o $@ $(OBJ)
mcaiger.o: ../aiger/aiger.h ../picosat/picosat.h makefile
clean:
	rm -f mcaiger *.o
.PHONY: all clean
