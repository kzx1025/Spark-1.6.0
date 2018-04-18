package cn.edu.hust.grid.soot.demo;

/**
 * Created by Administrator on 2015/7/20.
 */

class XNumber {
    private int value;

    public XNumber(int value) {
        this.value = value;
    }

    public int getValue() {
        return value;
    }

    public XNumber sum(XNumber other) {
        return new XNumber(value + other.value);
    }

}

class YNumber {
    double value;

    public YNumber(double value) {
        this.value = value;
    }

    public double getValue() {
        return value;
    }

    public YNumber sum(YNumber other) {
        return new YNumber(value + other.value);
    }

}

class ZNumber {
    long value;

    public ZNumber(long value) {
        this.value = value;
    }

    public long getValue() {
        return value;
    }

    public ZNumber sum(ZNumber other) {
        return new ZNumber(value + other.value);
    }

}

class Point2D {
    protected XNumber x;
    protected YNumber y;
    public XNumber[] a;
    public YNumber[] b;

    public XNumber getX() {
        return x;
    }

    public void setX(XNumber x) {
        this.x = x;
    }

    public YNumber getY() {
        return y;
    }

    public void setY(YNumber y) {
        this.y = y;
    }

    public void setA(XNumber a1, XNumber a2){
        a[0] = a1;
        a[1] = a2;
    }

}

class Line {
    protected Point2D point1;
    protected Point2D point2;
    protected Point2D[] line = new Point2D[2];

    public void setLine(Point2D point1, Point2D point2){
        line[0] = point1;
        line[1] = point2;
    }

    public void setPoint1(Point2D point1){
        this.point1=point1;
    }
    public void setPoint2(Point2D point2){
        this.point2=point2;
    }
}

class Point3D extends Point2D {
    protected ZNumber z;

    public void setZ(ZNumber z) {
        this.z = z;
    }

    public ZNumber getZ() {
        return z;
    }

    @Override
    public YNumber getY() {
        return y;
    }
}


public class Main {

    public static void main(String[] args) {
        Point3D p = new Point3D();
        p.setY(new YNumber(5.0));
        System.out.println(p.getY().getValue());
        /*double sum = p.getY().getValue() + 6.0;
        Point3D p1 = new Point3D();
        Line line1 = new Line();
        line1.setLine(p,p1);*/
    }

}
