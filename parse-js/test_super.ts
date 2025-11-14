class B {
    static a: any;
}
class C extends B {
    static z14 = ++super.a;
}