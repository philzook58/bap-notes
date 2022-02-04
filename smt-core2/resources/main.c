int fact(int x){
    int acc = 1;
    while(x > 0){
        acc *= x;
        x--;
    }
    return acc;
}