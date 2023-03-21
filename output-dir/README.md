## Layout output inspection 

In Table 2 and 3, for each row that is grayed, you can use the `diff` command to view how layouts are different.
We intentionally do not include this as a part of the artifact evaluation, as it requires expertise to 
understand why a layout is better than another. However, you are free to view the diff if you wish so.

For example, to view the difference between the layouts due to the `class-internal` benchmark for the code formatter, run:

```
diff classinternal@5750 classinternal@5751
```
