# Using KeY in External Projects

*weigl, 2020*


!!! abstract
    In this article, we present a tutorial for the setup of external project. 
    The setup embedds KeY as a git submodule, allowing modification of KeY 
    or using a different branch.
    
    

1. Create a folder and setup a new gradle project. Follow the wizard of gradle.
   Any JVM language should work.

   ```
   $ mkdir my-project; cd my-project
   $ gradle init my-project
   ```
   
2. Add KeY as a submodule 

  ```
  git submodule add https://key-project.org:key-public/key.git
  ```
  
  We use the HTTPS for an easier setup of CI pipelines. You can skip this step,
  if you want to create your project inside the KeY repository.
  

3. Add KeY into your gradle by adding following line into `settings.gradle`:

   ```
   includeBuild 'key/key'
   ```

   This makes the KeY gradle project available as dependencies into your project.
   You should now refer to them as dependencies in `build.gradle`:
   
   ```
   dependencies {
       implementation 'org.key_project:key.ui'
       implementation 'org.key_project:key.core'
   }

   repositories {
       mavenCentral()   // needed for various dependencies
       flatDir { dirs "lib", "key/key/key.core/lib" } //needed to find recoderKey.jar
   }
   ``` 

4. Now everything should work. You should be able to compile and test your
   project and use the KeY classes.
