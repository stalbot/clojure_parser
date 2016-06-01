package java_utils;

import java.util.Comparator;
import java.util.PriorityQueue;

/**
 * Created by Steven on 5/31/16.
 */
public class EasyPQueue extends PriorityQueue<EasyPQueue.SortableObject>  {

     public static class SortableObject {
        private final float first;
        private final Object second;

         public float getFirst() {
             return first;
         }

         public Object getSecond() {
             return second;
         }

        SortableObject(Number f, Object s) {
            first = f.floatValue();
            second = s;
        }
    }

    public void add(Object value, Number sorter) {
        add(new SortableObject(sorter, value));
    }

    public EasyPQueue() {
        super((SortableObject first, SortableObject second) ->
                second.first - first.first > 0 ? 1 : -1);
    }

}
