declare module "*.svg" {
    export const ReactComponent: any;    
  }


  declare module '*.css' {
      const content: {[className: string]: string};
      export default content;
  }
  