stack run > out.c
gcc -Iinclude/ out.c -fsanitize=address
./a.out
